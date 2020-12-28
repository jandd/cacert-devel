#!/usr/bin/perl -w

# CommModule - CAcert Communication Module
# Copyright (c) 2006-2020 by CAcert.org
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; version 2 of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

# Server (running on the certificate machine)

use strict;
use warnings;
use charnames qw/:full/;

use Carp;
use Device::SerialPort qw(:PARAM :STAT 0.07);
use Digest::SHA qw(sha1_hex);
use English qw/-no_match_vars/;
use File::Copy;
use File::CounterFile;
use IO::Handle;
use IO::Select;
use IPC::Open3;
use POSIX;
use Readonly;
use Time::HiRes qw(usleep);

# protocol version:
Readonly my $PROTOCOL_VERSION => 1;

# debug flag, set to 1 for increased logging, set to 2 to additionally log hexdumps
my $debug = 0;

# enable logging to stdout
my $log_stdout = 1;

# terminate in case of errors
my $paranoid = 1;

my $cps_url  = $ENV{'SIGNER_CPS_URL'}  || 'http://www.cacert.org/cps.php';
my $ocsp_url = $ENV{'SIGNER_OCSP_URL'} || 'http://ocsp.cacert.org/';

my $gpg_binary     = '/usr/bin/gpg';
my $openssl_binary = '/usr/bin/openssl';
my $xdelta_binary  = '/usr/bin/xdelta';

my $serialport      = $ENV{'SERIAL_PORT'}            || '/dev/ttyUSB0';
my $work            = $ENV{'SIGNER_WORKDIR'}         || './work';
my $ca_conf         = $ENV{'SIGNER_CA_CONFIG'}       || '/etc/ssl';
my $ca_basedir      = $ENV{'SIGNER_BASEDIR'}         || q{.};
my $gpg_keyring_dir = $ENV{'SIGNER_GPG_KEYRING_DIR'} || q{.};
my $gpg_key_id      = $ENV{'SIGNER_GPG_ID'}          || 'gpg@cacert.org';
my $gpg_cert_digest = $ENV{'SIGNER_GPG_CERT_DIGEST'} || 'SHA256';

Readonly::Hash my %IDENTITY_SYSTEMS => (
    '1' => 5,    # X.509
    '2' => 1     # OpenPGP
);
Readonly::Hash my %X509_MD_ALGORITHMS => (
    '0'  => q{},
    '1'  => '-md md5',
    '2'  => '-md sha1',
    '3'  => '-md rmd160',
    '8'  => '-md sha256',
    '9'  => '-md sha384',
    '10' => '-md sha512',
);
Readonly::Hash my %CA_TEMPLATES => (
    '0'  => 'client.cnf',
    '1'  => 'client-org.cnf',
    '2'  => 'client-codesign.cnf',
    '3'  => 'client-machine.cnf',
    '4'  => 'client-ads.cnf',
    '5'  => 'server.cnf',
    '6'  => 'server-org.cnf',
    '7'  => 'server-jabber.cnf',
    '8'  => 'ocsp.cnf',
    '9'  => 'timestamp.cnf',
    '10' => 'proxy.cnf',
    '11' => 'subca.cnf',
);

#End of configuration

########################################################

# Global variables
Readonly my $START_TIME        => 5 * 60;       # 5 minutes
Readonly my $MAGIC_BYTES       => 'rie4Ech7';
Readonly my $MAX_BLOCK_SIZE    => 2**24;
Readonly my $LENGTH_FIELD_SIZE => 3;

my Device::SerialPort $PortObj;
my IO::Select $sel;

local $ENV{'PATH'}            = '/usr/bin/:/bin';
local $ENV{'IFS'}             = "\n";
local $ENV{'LD_PRELOAD'}      = q{};
local $ENV{'LD_LIBRARY_PATH'} = q{};
local $ENV{'LANG'}            = q{};

#Logging functions:
sub sys_log {
    my ($log_entry) = @_;
    return if ( !defined $log_entry );
    my $date      = POSIX::strftime( '%Y-%m-%d',          localtime );
    my $timestamp = POSIX::strftime( '%Y-%m-%d %H:%M:%S', localtime );
    if ( open my $LOG, '>>', "logfile$date.txt" ) {
        print {$LOG} "$timestamp $log_entry"
            or croak("could not write to log file: $OS_ERROR");
        $LOG->autoflush();
        close $LOG or croak("could not close log file: $OS_ERROR");
    }
    else {
        croak("Could not open logfile$date.txt: $OS_ERROR");
    }
    if ( $log_stdout == 1 ) {
        print "$timestamp $log_entry" || croak("could not print: $OS_ERROR");
    }
    *STDOUT->autoflush();
    return;
}

sub log_error_and_die {
    my ($log_entry) = @_;
    sys_log("$log_entry\n");
    if ( $paranoid == 1 ) {
        croak $log_entry;
    }
    return;
}

sub read_file {
    my ($file_name) = @_;
    open my $READ_IN, '<', $file_name
        or croak "could not open file: $OS_ERROR";
    my $content = do {
        local $INPUT_RECORD_SEPARATOR = undef;
        <$READ_IN>;
    };
    close $READ_IN or croak("could not close $file_name: $OS_ERROR");
    return $content;
}

#Hexdump function: Returns the hexdump representation of a string
sub hexdump {
    my ($bytes) = @_;
    return q{} if ( !defined $bytes );
    my $content = q{};
    foreach ( 0 .. length($bytes) - 1 ) {
        $content .= sprintf '%02X ', unpack 'C', substr $bytes, $_, 1;
    }
    return $content;
}

Readonly my $ZERO_LENGTH_FIELD => "\N{NULL}\N{NULL}\N{NULL}";

#pack3 packs together the length of the data in 3 bytes and the data itself, size limited to 16MB. In case the data is more than 16 MB, it is ignored, and a 0 Byte block is transferred
sub pack3 {
    my ($bytes) = @_;
    return $ZERO_LENGTH_FIELD if ( !defined $bytes );
    my $data = ( length($bytes) >= $MAX_BLOCK_SIZE ) ? q{} : $bytes;
    my $len  = pack 'N', length $data;
    return substr( $len, 1, $LENGTH_FIELD_SIZE ) . $data;
}

#unpack3 unpacks packed data.
sub unpack3 {
    my ($data) = @_;
    if ( ( !defined $data ) or length($data) < $LENGTH_FIELD_SIZE ) {
        return;
    }
    if ( $debug >= 2 ) {
        sys_log( sprintf "hexdump: %s\n",
            hexdump( "\N{NULL}" . substr $data, 0, $LENGTH_FIELD_SIZE ) );
    }
    my $len = unpack 'N', "\N{NULL}" . substr $data, 0, $LENGTH_FIELD_SIZE;
    if ( $debug >= 1 ) {
        sys_log( sprintf "len3: %d length(): %d length()-3: %d\n",
            $len, length($data), ( length($data) - $LENGTH_FIELD_SIZE ) );
    }
    if ( length($data) - $LENGTH_FIELD_SIZE != $len ) {
        return;
    }
    return substr $data, $LENGTH_FIELD_SIZE;
}

#unpack3array extracts a whole array of concatenated packed data.
sub unpack3array {
    my ($data) = @_;
    my @result_array = ();
    if ( ( !defined $data ) or length($data) < $LENGTH_FIELD_SIZE ) {
        sys_log("Begin of structure corrupt\n");
        return ();
    }
    my $data_left = $data;
    while ( length($data_left) >= $LENGTH_FIELD_SIZE ) {
        if ( $debug >= 2 ) {
            sys_log(
                sprintf "hexdump: %s\n",
                hexdump(
                    "\N{NULL}" . substr $data_left,
                    0, $LENGTH_FIELD_SIZE
                )
            );
        }
        my $len = unpack 'N', "\N{NULL}" . substr $data_left, 0,
            $LENGTH_FIELD_SIZE;
        if ( $debug >= 1 ) {
            sys_log(
                sprintf "len3: %d length(): %d length()-3: %d\n",
                $len,
                length($data_left),
                ( length($data_left) - $LENGTH_FIELD_SIZE )
            );
        }
        if ( length($data_left) - $LENGTH_FIELD_SIZE < $len ) {
            sys_log("Structure cut off\n");
            return ();
        }
        push @result_array, substr $data_left, $LENGTH_FIELD_SIZE, $len;
        $data_left = substr $data_left, $LENGTH_FIELD_SIZE + $len;
    }
    if ( length($data_left) != 0 ) {
        sys_log("End of structure cut off\n");
        return ();
    }
    return @result_array;
}

Readonly my $DEFAULT_BAUD_RATE => 115_200;
Readonly my $DEFAULT_DATA_BITS => 8;
Readonly my $DEFAULT_STOP_BITS => 1;

sub serial_port_settings {
    my ($serial_port) = @_;
    if ( !defined $serial_port ) {
        log_error_and_die('Could not open Serial Port!');
    }
    $serial_port->baudrate($DEFAULT_BAUD_RATE);
    $serial_port->parity('none');
    $serial_port->databits($DEFAULT_DATA_BITS);
    $serial_port->stopbits($DEFAULT_STOP_BITS);
    return;
}

Readonly my $DEFAULT_MTU                 => 30;
Readonly my $SLEEP_MICROSECONDS_MIN      => 9000;
Readonly my $SLEEP_MICROSECONDS_PER_BYTE => 270;

#Raw send function over the Serial Interface  (+debugging)
sub send_data {
    my ($bytes) = @_;
    if ( !defined $bytes ) {
        return;
    }
    if ( $debug >= 1 ) {
        sys_log( sprintf "Sending %d\n", length $bytes );
    }
    if ( $debug >= 2 ) {
        sys_log( sprintf "Bytes to send: %s\n", hexdump($bytes) );
    }
    my $data  = $bytes;
    my $total = 0;
    while ( length $data ) {
        my $bytes_written =
            scalar( $PortObj->write( substr $data, 0, $DEFAULT_MTU ) ) || 0;

# On Linux, we have to wait to make sure it is being sent, and we dont loose any data.
        usleep(   $SLEEP_MICROSECONDS_PER_BYTE * $bytes_written
                + $SLEEP_MICROSECONDS_MIN );
        $total += $bytes_written;
        $data = substr $data, $bytes_written;
        if ( $debug >= 1 ) {
            sys_log(
                sprintf "wrote: %d bytes total: %d bytes left: %d bytes\n",
                $bytes_written, $total, length $data );
        }
    }
    return;
}

Readonly my $START_BYTE => chr 0x02;
Readonly my $ACK_BYTE   => chr 0x10;
Readonly my $RESET_BYTE => chr 0x11;

Readonly my $WAIT_FOR_HANDSHAKE_SECONDS          => 2;
Readonly my $WAIT_FOR_ACK_SECONDS                => 5;
Readonly my $WAIT_FOR_INITIAL_BYTES_MICROSECONDS => 1_000_000;

#Send data over the Serial Interface with handshaking:
#Warning: This function is implemented paranoid. It exits the program in case something goes wrong.
sub send_handshaked_paranoid {
    my ($bytes) = @_;
    if ( $debug >= 1 ) {
        sys_log("Sending response ...\n");
    }
    send_data($START_BYTE);

    if ( !scalar( $sel->can_read($WAIT_FOR_HANDSHAKE_SECONDS) ) ) {
        log_error_and_die('Handshake uncompleted. Connection lost!');
    }
    usleep($WAIT_FOR_INITIAL_BYTES_MICROSECONDS);
    my $data   = q{};
    my $length = 0;
    $length = read SER, $data, 1;
    if ( $length && $data eq $ACK_BYTE ) {
        if ( $debug >= 1 ) {
            sys_log("OK ...\n");
        }
        my $xor = 0;
        foreach ( 0 .. length($bytes) - 1 ) {
            $xor ^= unpack 'C', substr $bytes, $_, 1;
        }

        my $try_again = 1;
        while ( $try_again == 1 ) {
            send_data( $bytes . pack( 'C', $xor ) . $MAGIC_BYTES );

            if ( !scalar( $sel->can_read($WAIT_FOR_ACK_SECONDS) ) ) {
                log_error_and_die(
                    sprintf
                        'Packet receipt was not confirmed in %d seconds. Connection lost!',
                    $WAIT_FOR_ACK_SECONDS
                );
            }

            $data   = q{};
            $length = read SER, $data, 1;

            if ( $length && $data eq $ACK_BYTE ) {
                if ( $debug >= 1 ) {
                    sys_log("Sent successfully!...\n");
                }
                $try_again = 0;
            }
            elsif ( $length && $data eq $RESET_BYTE ) {
                $try_again = 1;
            }
            else {
                log_error_and_die( sprintf 'I cannot send! %d %s',
                    $length, unpack 'C', $data );
            }
        }
    }
    else {
        log_error_and_die("Cannot send! $length $data! Stopped sending.");
    }
    if ( $debug >= 1 ) {
        sys_log("Done sending response.\n");
    }
    return;
}

Readonly my $WAIT_FOR_INITIAL_DATA_SECONDS => 20;
Readonly my $MAX_TRIES                     => 10_000;
Readonly my $READ_BLOCK_SIZE               => 100;
Readonly my $MAGIC_BYTES_LENGTH            => length $MAGIC_BYTES;
Readonly my $CRC_LENGTH                    => 1;

sub receive_block {
    if ( !scalar( $sel->can_read($WAIT_FOR_INITIAL_DATA_SECONDS) ) ) {
        log_error_and_die("Could not read: $OS_ERROR");
    }
    my $data   = q{};
    my $length = read SER, $data, 1, 0;

    if ( $debug >= 2 ) {
        sys_log( sprintf "Data: %s\n", hexdump($data) );
    }

    if ( $data eq $START_BYTE ) {
        if ( $debug >= 1 ) {
            sys_log("Start received, sending OK\n");
        }
        send_data($ACK_BYTE);

        my $block          = q{};
        my $block_finished = 0;
        my $tries          = $MAX_TRIES;

        while ( $block_finished != 1 ) {
            if ( ( $tries-- ) <= 0 ) {
                log_error_and_die('Tried reading too often');
            }

            $data = q{};
            if ( !scalar( $sel->can_read($WAIT_FOR_HANDSHAKE_SECONDS) ) ) {
                log_error_and_die('Timeout reading data!');
            }
            $length = read SER, $data, $READ_BLOCK_SIZE, 0;
            if ( $length > 0 ) {
                $block .= $data;
            }
            if ( $debug >= 1 ) {
                sys_log( sprintf "Received: %d %d\n", $length,
                    length $block );
            }
            $block_finished =
                defined( unpack3 substr $block,
                0, -( $MAGIC_BYTES_LENGTH + $CRC_LENGTH ) )
                ? 1
                : 0;

            if ( ( !$block_finished )
                and
                substr( $block, -$MAGIC_BYTES_LENGTH, $MAGIC_BYTES_LENGTH )
                eq $MAGIC_BYTES )
            {
                sys_log("BROKEN Block detected!\n");
                send_data($RESET_BYTE);
                $block          = q{};
                $block_finished = 0;
                $tries          = $MAX_TRIES;
            }

            if ( $block_finished && !check_crc($block) ) {
                sys_log("CRC error\n");
                send_data($RESET_BYTE);
                $block          = q{};
                $block_finished = 0;
                $tries          = $MAX_TRIES;
            }
        }
        if ( $debug >= 2 ) {
            sys_log( sprintf "Block done: %s\n", hexdump($block) );
        }
        send_data($ACK_BYTE);
        if ( $debug >= 1 ) {
            sys_log("Returning block\n");
        }
        return ($block);
    }
    else {
        if ( length($data) == 0 ) {
            log_error_and_die('Error: No answer received, timeout.');
        }
        log_error_and_die( sprintf 'Error: Wrong start byte: %s!',
            hexdump($data) );
    }

    sys_log("Waiting on next request ...\n");
    return;
}

#Checks the CRC of a received block for validity
#Returns 1 upon successful check and 0 for a failure
sub check_crc {
    my ($block) = @_;
    return 0 if ( length($block) < 1 );
    return 1 if ( $block eq "\N{NULL}" );
    my $xor                   = 0;
    my $trailing_bytes_length = $CRC_LENGTH + $MAGIC_BYTES_LENGTH;
    foreach ( 0 .. length($block) - $trailing_bytes_length - 1 ) {
        $xor ^= unpack 'C', substr $block, $_, 1;
    }
    return (
        $xor eq unpack 'C',        substr $block,
        -($trailing_bytes_length), $CRC_LENGTH
        )
        ? 1
        : 0;
}

#Formatting and sending a Response packet
sub send_response {
    my ( $version, $response_type, $arg_ref ) = @_;

    my $reserved1 = exists $arg_ref->{reserved1} ? $arg_ref->{reserved1} : 0;
    my $reserved2 = exists $arg_ref->{reserved2} ? $arg_ref->{reserved2} : 0;
    my $content = exists $arg_ref->{content} ? $arg_ref->{content} : q{};
    my $argument1 =
        exists $arg_ref->{argument1} ? $arg_ref->{argument1} : q{};
    my $argument2 =
        exists $arg_ref->{argument2} ? $arg_ref->{argument2} : q{};

    send_handshaked_paranoid(
        pack3(
            pack3(
                pack 'C*',  $version, $response_type,
                $reserved1, $reserved2
                )
                . pack3($content)
                . pack3($argument1)
                . pack3($argument2)
        )
    );
    return;
}

#Checks the parameters, whether the certificate system (OpenPGP, X.509, ...) is available,
#whether the specified root key is available, whether the config file is available, ...
#Returns 1 upon success, and dies upon error!
sub check_identity_system {
    my ( $id_system, $root, $template, $hash ) = @_;
    if ( !defined $CA_TEMPLATES{$template} ) {
        log_error_and_die( sprintf 'CA template %s unknown!', $template );
    }
    if ( !defined $X509_MD_ALGORITHMS{$hash} ) {
        log_error_and_die( sprintf "Hash algorithm %s unknown!\n", $hash );
    }
    if ( defined $IDENTITY_SYSTEMS{$id_system} ) {
        if ( $root < $IDENTITY_SYSTEMS{$id_system} ) {
            return 1;
        }
        else {
            log_error_and_die(
                sprintf
                    'Identity system %s has only %d root keys, key %d does not exist.',
                $id_system, $IDENTITY_SYSTEMS{$id_system}, $root );
        }
    }
    else {
        log_error_and_die( sprintf 'Identity system %s not supported',
            $id_system );
    }

    return 0;
}

#Selects the specified config file for OpenSSL and makes sure that the specified config file exists
#Returns the full path to the config file
sub x509_config_file {
    my ( $root, $template ) = @_;
    my $openssl_configuration = q{};
    if ( $root == 0 ) {
        $openssl_configuration = "$ca_conf/openssl-$CA_TEMPLATES{$template}";
    }
    elsif ( $root == 1 ) {
        $openssl_configuration = "$ca_conf/class3-$CA_TEMPLATES{$template}";
    }
    elsif ( $root == 2 ) {
        $openssl_configuration = "$ca_conf/class3s-$CA_TEMPLATES{$template}";
    }
    else {
        $openssl_configuration =
            "$ca_conf/root$root/$CA_TEMPLATES{$template}";
    }

    # Check that the config file exists
    if ( !-f $openssl_configuration ) {
        log_error_and_die(
            sprintf 'OpenSSL configuration file %s does not exist!',
            $openssl_configuration );
    }
    return $openssl_configuration;
}

Readonly my $DIRECTORY_MODE  => oct 700;
Readonly my $DIRECTORY_SPLIT => 1000;

sub create_workspace {
    mkdir "$work", $DIRECTORY_MODE;
    my $id = ( File::CounterFile->new( "$work/.counter", '0' ) )->inc;
    mkdir sprintf( '%s/%d', $work, int( $id / $DIRECTORY_SPLIT ) ),
        $DIRECTORY_MODE;
    my $wid = sprintf '%s/%d/%d', $work, int( $id / $DIRECTORY_SPLIT ),
        ( $id % $DIRECTORY_SPLIT );
    mkdir $wid, $DIRECTORY_MODE;
    sys_log("Created working directory: $wid\n");
    return $wid;
}

Readonly::Hash my %KNOWN_COMMANDS => { NUL => 0, SIGN => 1, REVOKE => 2 };
Readonly::Hash my %RESPONSE_TYPES => { NUL => 0, SIGN => 1, REVOKE => 2 };

sub openssl_sign_certificate {
    my ($arg_ref) = @_;

    my $md_algorithm           = $arg_ref->{md_algorithm};
    my $openssl_config         = $arg_ref->{openssl_config};
    my $cmd                    = $arg_ref->{cmd};
    my $request_file           = $arg_ref->{request_file};
    my $certificate_file       = $arg_ref->{certificate_file};
    my $days                   = $arg_ref->{days};
    my $x509v3_extensions_file = $arg_ref->{extension_file};

    my $stdout = IO::Handle->new();

    my $command = sprintf
        '%s ca %s -config %s %s %s -out %s -days %d -key test -batch %s 2>&1',
        $openssl_binary, $md_algorithm, $openssl_config, $cmd,
        $request_file, $certificate_file, $days, $x509v3_extensions_file;
    my $pid = open3( undef, $stdout, $stdout, $command );
    sys_log( scalar <$stdout> );
    waitpid $pid, 0;

    my $content = read_file($certificate_file);
    $content =~ s/^.*-----BEGIN/-----BEGIN/xms;
    return $content;
}

sub get_subject_command {
    my ( $spkac, $request, $subject ) = @_;

    if ( $request =~ m/SPKAC\s*=/xms ) {
        if ( !$spkac == 1 ) {
            sys_log("WARNING missing SPKAC flag but SPKAC content\n");
        }
        return '-spkac';
    }
    if ( $spkac == 1 ) {
        sys_log("WARNING SPKAC flag found but non SPKAC request received\n");
    }
    return sprintf '-subj "%s" -in', $subject;
}

sub sign_x509 {
    my ($arg_ref) = @_;

    my $root     = $arg_ref->{root};
    my $template = $arg_ref->{template};
    my $hash     = $arg_ref->{hash};
    my $days     = $arg_ref->{days};
    my $request  = $arg_ref->{request};
    my $san      = $arg_ref->{san};
    my $subject  = $arg_ref->{subject};
    my $spkac    = $arg_ref->{spkac};

    my $wid = create_workspace();

    my $openssl_config = x509_config_file( $root, $template );

    sys_log("Subject: $subject\n");
    sys_log("SAN: $san\n");

    $subject =~ s/\\x([[:xdigit:]]{2})/pack("C", hex($1))/xmsegi;
    $san     =~ s/\\x([[:xdigit:]]{2})/pack("C", hex($1))/xmsegi;

    if ( $san =~ m/[\s\x00#"'\\]/xms ) {
        log_error_and_die('Invalid characters in SubjectAltName!');
    }
    if ( $subject =~ m/[\s\x00#"'\\]/xms ) {
        log_error_and_die( sprintf 'Invalid characters in Subject: %s - %s',
            hexdump($subject), $subject );
    }

    sys_log("Subject: $subject\n");
    sys_log("SAN: $san\n");

    my $extension_filename     = "$wid/extfile";
    my $x509v3_extensions_file = q{};

    # TODO: Shouldn't we really do that for all and not only for server certs?
    if ( $CA_TEMPLATES{$template} =~ m/server/xms ) {
        my @lines = ();
        push @lines, 'basicConstraints = critical, CA:FALSE';
        push @lines,
            'keyUsage = critical, digitalSignature, keyEncipherment, keyAgreement';
        push @lines,
            'extendedKeyUsage = clientAuth, serverAuth, nsSGC, msSGC';
        push @lines, "authorityInfoAccess = OCSP;URI:$ocsp_url";

        my $crl_url = q{};
        if ( $root == 0 ) {
            $crl_url = 'http://crl.cacert.org/revoke.crl';
        }
        elsif ( $root == 1 ) {
            $crl_url = 'http://crl.cacert.org/class3-revoke.crl';
        }
        elsif ( $root == 2 ) {
            $crl_url = 'http://crl.cacert.org/class3s-revoke.crl';
        }
        else {
            $crl_url = "http://crl.cacert.org/root${root}.crl";
        }

        push @lines, "crlDistributionPoints = URI:$crl_url";
        if ( ( length $san ) > 0 ) {
            push @lines, "subjectAltName = $san";
        }

        if ( open my $OUT, '>', $extension_filename ) {
            print {$OUT} join "\n", @lines
                or
                log_error_and_die("could not write to $extfile:: $OS_ERROR");
            close $OUT
                or log_error_and_die("could not close $extfile:: $OS_ERROR");
            $x509v3_extensions_file = " -extfile $extension_filename";
        }
        else {
            log_error_and_die(
                "could not open $extension_filename: $OS_ERROR");
        }
    }

    my $cmd              = get_subject_command( $spkac, $request, $subject );
    my $request_file     = "$wid/request.csr";
    my $certificate_file = "$wid/output.crt";
    open my $OUT, '>', $request_file
        or log_error_and_die(
        "could not open $request_file for writing: $OS_ERROR");
    print {$OUT} $request
        or log_error_and_die("could not write to $request_file: $OS_ERROR");
    close $OUT
        or log_error_and_die("could not close $request_file: $OS_ERROR");

    my $content = openssl_sign_certificate(
        {   md_algorithm     => $X509_MD_ALGORITHMS{$hash},
            openssl_config   => $openssl_config,
            cmd              => $cmd,
            request_file     => $request_file,
            certificate_file => $certificate_file,
            days             => $days,
            extension_file   => $x509v3_extensions_file
        }
    );
    sys_log "Sending response ...\n";
    send_response( $PROTOCOL_VERSION, $RESPONSE_TYPES{SIGN},
        { content => $content } );
    sys_log "Done.\n";

    if ( $debug != 0 ) {
        unlink $certificate_file;
        unlink $request_file;
        unlink $extension_filename;
    }
    unlink "$wid";
    return;
}

sub copy_keyring_to_workspace {
    my ( $wid, $root ) = @_;

    my $secring;
    my $pubring;
    if ( -d "$gpg_keyring_dir/gpg_root_$root" ) {
        $secring = "$gpg_keyring_dir/gpg_root_$root/secring.gpg";
        $pubring = "$gpg_keyring_dir/gpg_root_$root/pubring.gpg";
    }
    else {
        $secring = "$gpg_keyring_dir/secring$root.gpg";
        $pubring = "$gpg_keyring_dir/pubring$root.gpg";
    }

    if ( !-f $secring || !-f $pubring ) {
        log_error_and_die("GPG secret key ring $secring not found!");
    }

    copy( $secring, "$wid/secring.gpg" );
    copy( $pubring, "$wid/pubring.gpg" );
    return;
}

Readonly my $RE_GPG_PREFIX   => qr/^\[GNUPG:\][ ]/xms;
Readonly my $RE_GPG_GET_BOOL => qr/GET_BOOL[ ]/xms;
Readonly my $RE_GPG_GET_LINE => qr/GET_LINE[ ]/xms;

sub gpg_find_key_id {
    my ( $homedir, $request_file ) = @_;
    my $key_id = undef;

    sys_log("Running GnuPG in $homedir...\n");
    my ( $stdin, $stdout, $stderr ) =
        ( IO::Handle->new(), IO::Handle->new(), IO::Handle->new() );

    my $command = sprintf
        '%s --no-tty --homedir %s --command-fd 0 --status-fd 1 --logger-fd 2 --with-colons --import %s',
        $gpg_binary, $homedir, $request_file;
    if ( $debug >= 1 ) {
        sys_log( sprintf "%s\n", $command );
    }

    my $pid = open3( $stdin, $stdout, $stderr, $command );
    if ( $pid == 0 ) {
        log_error_and_die('Cannot fork GnuPG.');
    }

    my $re_ignored_responses = qr{
    (?: GOT_IT | ALREADY_SIGNED | GOOD_PASSPHRASE | KEYEXPIRED | SIGEXPIRED | IMPORT_OK | IMPORT_RES )}xms;

    local $INPUT_RECORD_SEPARATOR = "\n";
    while (<$stdout>) {
        sys_log("Received from GnuPG: $_");
        if (m/$RE_GPG_PREFIX $RE_GPG_GET_BOOL keyedit[.]setpref[.]okay/xms) {
            print {$stdin} "no\n"
                or log_error_and_die(
                "Could not write to stdin of gpg process: $OS_ERROR");
        }
        elsif (m/$RE_GPG_PREFIX IMPORTED[ ]([[:xdigit:]]{16})/xms) {
            if ( defined $key_id ) {
                log_error_and_die('More than one OpenPGP sent at once!');
            }
            $key_id = $1;
        }
        elsif (m/$RE_GPG_PREFIX $re_ignored_responses/xms) {
            if ( $debug >= 1 ) {
                sys_log("$_ -> $1\n");
            }
        }
        elsif (m/$RE_GPG_PREFIX NODATA/xms) {

            # To crash or not to crash, that's the question.
        }
        else {
            log_error_and_die("ERROR: UNKNOWN $_");
        }
    }

    while (<$stderr>) {
        sys_log("Received from GnuPG on stderr: $_");
    }

    waitpid $pid, 0;

    if ( !defined $key_id ) {
        log_error_and_die('No KeyID found!');
    }
    return $key_id;
}

sub gpg_sign_key {
    my ( $homedir, $key_id, $days ) = @_;

    my ( $stdin, $stdout, $stderr ) =
        ( IO::Handle->new(), IO::Handle->new(), IO::Handle->new() );

    local $ENV{'LANG'} = q{};

    my $command =
        sprintf
        '%s --no-tty --default-key %s --homedir %s --default-cert-expire %dd'
        . ' --ask-cert-expire --cert-policy-url %s --command-fd 0 --cert-digest-algo %s'
        . ' --status-fd 1 --logger-fd 2 --sign-key %s',
        $gpg_binary, $gpg_key_id, $homedir, $days, $cps_url, $gpg_cert_digest,
        $key_id;
    if ( $debug >= 1 ) {
        sys_log( sprintf "%s\n", $command );
    }

    my $pid = open3( $stdin, $stdout, $stderr, $command );

    if ( $pid == 0 ) {
        log_error_and_die('Cannot fork GnuPG.');
    }
    sys_log "Got PID $pid\n";

    my $re_sign_uid_yes =
        qr/(?: okay | expire_okay | replace_expired_okay | dupe_okay )/xms;
    my $re_yes_flags =
        qr/(?:keyedit[.]sign_all[.]okay | sign_uid[.]$re_sign_uid_yes)/xms;

    my $re_sign_uid_no = qr/(?: revoke_okay | nosig_okay| v4_on_v3_okay )/xms;
    my $re_no_flags =
        qr/(?:keyedit[.](?:sign_revoked|setpref)[.]okay | sign_uid[.]$re_sign_uid_no)/xms;

    my $re_ignored_responses =
        qr/(?: GOT_IT | ALREADY_SIGNED| GOOD_PASSPHRASE| KEYEXPIRED | SIGEXPIRED )/xms;

    while (<$stdout>) {
        sys_log("Received from GnuPG: $_");
        if (m/$RE_GPG_PREFIX $RE_GPG_GET_BOOL $re_yes_flags/xms) {
            print {$stdin} "yes\n"
                or log_error_and_die(
                "could not write to stdin of gpg process: $OS_ERROR");
        }
        elsif (m/$RE_GPG_PREFIX $RE_GPG_GET_LINE siggen[.]valid\s?$/xms) {
            print {$stdin} "$days\n"
                or log_error_and_die(
                "could not write to stdin of gpg process: $OS_ERROR");
        }
        elsif (m/$RE_GPG_PREFIX $RE_GPG_GET_LINE sign_uid[.]expire\s?$/xms) {
            sys_log(
                "DETECTED: Do you want your signature to expire at the same time? (Y/n) -> yes\n"
            );
            print {$stdin} "no\n"
                or log_error_and_die(
                "could not write to stdin of gpg process: $OS_ERROR");
        }
        elsif (m/$RE_GPG_PREFIX $RE_GPG_GET_BOOL $re_no_flags/xms) {
            print {$stdin} "no\n"
                or log_error_and_die(
                "could not write to stdin of gpg process: $OS_ERROR");
        }
        elsif (m/$RE_GPG_PREFIX $RE_GPG_GET_BOOL sign_uid[.]expired_okay/xms)
        {
            sys_log("The key has already expired!!!\n");
            print {$stdin} "no\n"
                or log_error_and_die(
                "could not write to stdin of gpg process: $OS_ERROR");
        }
        elsif (m/$RE_GPG_PREFIX $re_ignored_responses/xms) {
            if ( $debug >= 1 ) {
                sys_log("read $1\n");
            }
        }
        elsif (m/$RE_GPG_PREFIX NODATA/xms) {

            # To crash or not to crash, thats the question.
        }
        else {
            log_error_and_die("ERROR: UNKNOWN $_");
        }
    }

    while (<$stderr>) {
        sys_log("Received from GnuPG on stderr: $_");
    }

    waitpid $pid, 0;
    return;
}

sub gpg_export_key {
    my ( $homedir, $key_id ) = @_;

    my $stdout = IO::Handle->new();
    my $command =
        "$gpg_binary --no-tty --homedir $homedir --export --armor $key_id";
    my $pid    = open3( undef, $stdout, undef, $command );
    my @output = <$stdout>;
    waitpid $pid, 0;

    my $content = join q{}, @output;
    $content =~ s/^.*-----BEGIN/-----BEGIN/xms;
    if ( $debug >= 1 ) {
        sys_log($content);
    }
    return $content;
}

sub sign_openpgp {
    my ($arg_ref) = @_;

    my $root    = $arg_ref->{root};
    my $days    = $arg_ref->{days};
    my $request = $arg_ref->{request};

    my $wid = create_workspace();
    copy_keyring_to_workspace( $wid, $root );

    my $request_filename = "$wid/request.key";
    open my $OUT, '>', $request_filename
        or log_error_and_die(
        "could not open OpenPGP public key file $request_filename for writing: $OS_ERROR"
        );
    print {$OUT} $request
        or log_error_and_die("could not write OpenPGP public key: $OS_ERROR");
    close $OUT
        or log_error_and_die(
        "could not close OpenPGP public key file: $OS_ERROR");

    my $homedir = "$wid/";
    my $key_id  = gpg_find_key_id( $homedir, $request_filename );
    if ( $debug >= 1 ) {
        sys_log("Running GnuPG to Sign...\n");
    }
    gpg_sign_key( $homedir, $key_id, $days );
    if ( $debug >= 1 ) {
        sys_log("Running GPG to export...\n");
    }

    my $content = gpg_export_key( $homedir, $key_id );
    send_response( $PROTOCOL_VERSION, $RESPONSE_TYPES{SIGN},
        { content => $content } );

    if ( $debug != 0 ) {
        unlink $request_filename;
    }

    unlink "$wid/secring.gpg";
    unlink "$wid/pubring.gpg";
    unlink "$wid";
    return;
}

sub openssl_revoke_certificate {
    my ( $md_algorithm, $openssl_config, $request_filename ) = @_;

    my $stdout = IO::Handle->new();

    my $command =
        "$openssl_binary ca $md_algorithm -config $openssl_config -key test -batch -revoke $request_filename";
    my $pid = open3( undef, $stdout, $stdout, $command );
    if ( $debug >= 1 ) {
        sys_log("output from $command:\n<$stdout");
    }
    waitpid $pid, 0;
    return;
}

sub openssl_generate_crl {
    my ( $md_algorithm, $openssl_config, $wid ) = @_;

    my $stdout = IO::Handle->new();

    my $temporary_crl = "$wid/cacert-revoke.crl";
    my $command =
        "$openssl_binary ca $md_algorithm -config $openssl_config -key test -batch -gencrl -crldays 7 -crlexts crl_ext -out $temporary_crl";
    my $pid = open3( undef, $stdout, $stdout, $command );
    if ( $debug >= 1 ) {
        sys_log("output from $command:\n<$stdout>");
    }
    close $stdout or log_error_and_die("could not close stdout: $OS_ERROR");
    waitpid $pid, 0;

    $stdout = IO::Handle->new();
    $command =
        "$openssl_binary crl -inform PEM -in $temporary_crl -outform DER";
    $pid = open3( undef, $stdout, $stdout, $command );
    my $content;
    do {
        local $INPUT_RECORD_SEPARATOR = undef;
        $content = <$stdout>;
    };
    close $stdout or log_error_and_die("could not close stdout: $OS_ERROR");
    waitpid $pid, 0;
    unlink $temporary_crl;

    return $content;
}

sub build_crl_delta {
    my ( $old_crl, $new_crl, $root, $wid ) = @_;

    my $stdout         = IO::Handle->new();
    my $xdelta_patch   = "$wid/delta$root.diff";
    my $xdelta_command = sprintf '%s delta %s %s %s', $xdelta_binary,
        $old_crl, $new_crl, $xdelta_patch;
    my $pid = open3( undef, $stdout, $stdout, $xdelta_command );
    if ( $debug >= 1 ) {
        local $INPUT_RECORD_SEPARATOR = undef;
        sys_log( sprintf 'xdelta output: %s', <$stdout> );
    }
    waitpid $pid, 0;
    my $content = read_file($xdelta_patch);
    unlink $xdelta_patch;
    return $content;
}

sub delete_old_crls {
    my ( $root, $client_hash ) = @_;

    sys_log("Deleting old CRLs...\n");
    foreach ( glob "$ca_basedir/currentcrls/$root/*" ) {
        if ( $_ ne "$ca_basedir/currentcrls/$root/$client_hash.crl" ) {
            sys_log("Deleting $_\n");
            unlink;
        }
    }
    sys_log("Done with deleting old CRLs.\n");
    return;
}

sub revoke_certificate {
    my ( $request, $wid, $md_algorithm, $openssl_config ) = @_;

    if ( length $request > 0 ) {
        my $request_filename = "$wid/request.crt";
        open my $OUT, '>', $request_filename
            or log_error_and_die(
            "could not open request file $request_filename for writing: $OS_ERROR"
            );
        print {$OUT} $request
            or log_error_and_die(
            "could not write request to $request_filename: $OS_ERROR");
        close $OUT
            or log_error_and_die(
            "could not close request file $request_filename: $OS_ERROR");
        openssl_revoke_certificate( $md_algorithm, $openssl_config,
            $request_filename );
    }
    return;
}

Readonly my $EMPTY_STRING_HASH => sha1_hex(q{});

sub revoke_x509 {
    my ($arg_ref) = @_;

    my $root     = $arg_ref->{root};
    my $template = $arg_ref->{template};
    my $hash     = $arg_ref->{hash};
    my $request  = $arg_ref->{request};

    my $client_hash = $arg_ref->{client_hash};

    if ( !$client_hash =~ m/^[[:xdigit:]]+$/xms ) {
        log_error_and_die('Invalid characters in CRL hash!');
    }

    sys_log("Revoke X.509 for $root\n");
    sys_log("Current hash from client: $client_hash\n");

    my $is_current = 0;
    my $current_hash;

    if ( -f "revoke-root$root.crl" ) {
        $current_hash = sha1_hex( read_file("revoke-root$root.crl") );
    }
    else {
        $current_hash = $EMPTY_STRING_HASH;
    }

    sys_log("Current hash on signer $current_hash\n");

    if ( $client_hash eq $current_hash ) {
        sys_log("Hash matches current CRL.\n");
        delete_old_crls( $root, $client_hash );
        if ( $client_hash eq $EMPTY_STRING_HASH ) {
            sys_log("Client has empty CRL\n");
        }
        else {
            $is_current = 1;
        }
    }

    my $wid            = create_workspace();
    my $openssl_config = x509_config_file( $root, $template );

    revoke_certificate( $request, $X509_MD_ALGORITHMS{$hash},
        $wid, $openssl_config );

    my $crl_content = openssl_generate_crl( $X509_MD_ALGORITHMS{$hash},
        $openssl_config, $wid );

    mkdir "$ca_basedir/currentcrls/$root";
    my $new_crl_name = sprintf "$ca_basedir/currentcrls/$root/%s.crl",
        sha1_hex($crl_content);
    open my $OUT, '>', "$new_crl_name"
        or log_error_and_die(
        "could not open CRL file $new_crl_name for writing: $OS_ERROR");
    print {$OUT} $crl_content
        or log_error_and_die("could not write to $new_crl_name $OS_ERROR");
    close $OUT
        or log_error_and_die("could not close $new_crl_name: $OS_ERROR");

    if ( $is_current == 1 ) {
        sys_log("send current CRL delta...\n");
        send_response(
            $PROTOCOL_VERSION,
            $RESPONSE_TYPES{REVOKE},
            {   content => build_crl_delta(
                    "revoke-root$root.crl", $new_crl_name, $root, $wid
                )
            }
        );
    }
    else {
        if ( -f "$ca_basedir/currentcrls/$root/$client_hash.crl" ) {
            sys_log("send CRL delta for client CRL...\n");
            send_response(
                $PROTOCOL_VERSION,
                $RESPONSE_TYPES{REVOKE},
                {   content => build_crl_delta(
                        "$ca_basedir/currentcrls/$root/$client_hash.crl",
                        $new_crl_name, $root, $wid
                    )
                }
            );
        }
        else {
            sys_log("Out of Sync! Sending full CRL...\n");
            send_response( $PROTOCOL_VERSION, $RESPONSE_TYPES{REVOKE},
                { content => read_file($new_crl_name) } );
        }
    }

    open my $CRL_OUT, '>', "revoke-root$root.crl"
        or
        log_error_and_die("could not open CRL file for writing: $OS_ERROR");
    print {$CRL_OUT} $crl_content
        or log_error_and_die("could not write to CRL file: $OS_ERROR");
    close $CRL_OUT
        or log_error_and_die("could not close CRL file: $OS_ERROR");

    if ( $debug >= 1 ) {
        sys_log("Done.\n");
    }
    return;
}

Readonly my $EXPECTED_FIELDS_IN_BLOCK => 4;
Readonly my $EXPECTED_HEADER_LENGTH   => 9;

sub analyze_block {
    my ($block) = @_;
    if ( $debug >= 1 ) {
        sys_log("analyzing ...\n");
    }
    if ( $debug >= 2 ) {
        sys_log( sprintf "%s\n", hexdump($block) );
    }

    my @fields = unpack3array( substr $block,
        $LENGTH_FIELD_SIZE, -( $MAGIC_BYTES_LENGTH + $CRC_LENGTH ) );
    if ( scalar(@fields) != $EXPECTED_FIELDS_IN_BLOCK ) {
        foreach my $field (@fields) {
            sys_log( sprintf "%s\n%s\n", hexdump($field), $field );
        }
        log_error_and_die(
            sprintf 'Wrong number of parameters: %d instead of %d',
            scalar @fields,
            $EXPECTED_FIELDS_IN_BLOCK
        );
    }
    my ( $header, $request, $san, $subject ) = @fields;

    if ( $debug >= 2 ) {
        sys_log( sprintf "Header: %s\n", hexdump($header) );
    }
    my @header_bytes = unpack 'CCCCCCnC', $header;

    if ( length($header) != $EXPECTED_HEADER_LENGTH ) {
        log_error_and_die(
            sprintf 'Header has wrong length: %d! Should be %d bytes.',
            length $header,
            $EXPECTED_HEADER_LENGTH
        );
    }
    my ( $version, $command, $id_system, $root, $template, $hash, $days,
        $spkac )
        = @header_bytes;

    if ( $version != $PROTOCOL_VERSION ) {
        log_error_and_die(
            sprintf
                'Version mismatch. Server does not support version %d, server only supports version %d!',
            $version, $PROTOCOL_VERSION
        );
    }

    if ( $command == $KNOWN_COMMANDS{NUL} ) {
        sys_log("Received NUL request\n");
        if ( $request =~ m{^\d+[.]\d+$}xms ) {
            open my $OUT, '>', 'timesync.sh'
                or log_error_and_die("could not open timesync.sh: $OS_ERROR");
            print {$OUT} "date -u '$request'\n"
                or log_error_and_die(
                "could not write to timesync.sh: $OS_ERROR");
            print {$OUT} "hwclock --systohc\n"
                or log_error_and_die(
                "could not write to timesync.sh: $OS_ERROR");
            close $OUT
                or
                log_error_and_die("could not close timesync.sh: $OS_ERROR");
        }
        send_response( $PROTOCOL_VERSION, $RESPONSE_TYPES{NUL}, {} );
        sys_log("Handled NUL request\n");
    }
    elsif ( $command == $KNOWN_COMMANDS{SIGN} ) {
        sys_log("Received SIGN request\n");
        check_identity_system( $id_system, $root, $template, $hash );
        if ( $id_system == 1 ) {
            sign_x509(
                {   root     => $root,
                    template => $template,
                    hash     => $hash,
                    days     => $days,
                    request  => $request,
                    san      => $san,
                    subject  => $subject,
                    spkac    => $spkac,
                }
            );
        }
        elsif ( $id_system == 2 ) {
            sign_openpgp(
                {   root    => $root,
                    days    => $days,
                    request => $request,
                }
            );
        }
        sys_log("Handled SIGN request\n");
    }
    elsif ( $command == $KNOWN_COMMANDS{REVOKE} ) {
        sys_log("Received REVOKE request\n");
        check_identity_system( $id_system, $root, $template, $hash );
        if ( $id_system == 1 ) {
            revoke_x509(
                {   root        => $root,
                    template    => $template,
                    hash        => $hash,
                    request     => $request,
                    client_hash => $subject
                }
            );
        }
        sys_log("Handled REVOKE request\n");
    }
    else {
        log_error_and_die('Unknown command');
    }
    return;
}

# Start of execution
my $timestamp = POSIX::strftime( '%Y-%m-%d %H:%M:%S', localtime );
sys_log("Starting server at $timestamp\n");

mkdir "$work", $DIRECTORY_MODE;
mkdir "$ca_basedir/currentcrls";

sys_log("Opening serial interface:\n");

#We have to open the SerialPort and close it again, so that we can bind it to a Handle
$PortObj = Device::SerialPort->new($serialport);
serial_port_settings($PortObj);
$PortObj->save('serialserver.conf');

undef $PortObj;

$PortObj = tie( *SER, 'Device::SerialPort', 'serialserver.conf' )
    || log_error_and_die(
    "Can't tie using Configuration_File_Name: $OS_ERROR");

if ( !defined $PortObj ) {
    log_error_and_die('Could not open Serial Interface!');
}
serial_port_settings($PortObj);

sys_log("Serial interface opened: $PortObj\n");

#Creating select() selector for improved reading:
$sel = IO::Select->new( \*SER );

local $SIG{INT}  = \&signal_handler;
local $SIG{TERM} = \&signal_handler;

sub signal_handler {
    log_error_and_die("caught signal $OS_ERROR");
    return;
}

sys_log("Server started. Waiting 5 minutes for contact from client ...\n");

#When started, we wait for 5 minutes for the client to connect:
my @ready = $sel->can_read($START_TIME);

my $count = 0;

Readonly my $WAIT_FOR_CLIENT_SECONDS => 15;

#As soon as the client connected successfully, the client has to send a request faster than every 10 seconds
while ( @ready =
    $sel->can_read($WAIT_FOR_CLIENT_SECONDS) && -f './server.pl-active' )
{
    my $data = q{};

    $data = receive_block();
    analyze_block($data);

    $count++;

    if ( $debug >= 1 ) {
        sys_log(
            sprintf "%d requests processed. Waiting on next request ...\n",
            $count );
    }
}

log_error_and_die('Timeout! No data from client anymore!');
