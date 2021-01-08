#!/usr/bin/perl -w

# CommModule - CAcert Communication Module
# Copyright (C) 2006-2020  CAcert Inc.
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

# Production Client / CommModule

use strict;
use warnings;
use charnames qw/:full/;

use Carp;
use DBI;
use Device::SerialPort qw(:PARAM :STAT 0.07);
use Digest::SHA qw(sha1_hex);
use English qw/-no_match_vars/;
use File::Basename qw(dirname);
use File::Copy;
use File::CounterFile;
use IO::Select;
use IO::Socket;
use IPC::Open3;
use Locale::gettext;
use Email::MIME;
use Net::SMTP;
use POSIX;
use Readonly;
use Time::HiRes qw(usleep);

my $paranoid = 1;

# seem like debug 2 breaks checksum byte
my $debug = 0;

my $log_stdout = 1;

my $gpg_binary     = '/usr/bin/gpg';
my $openssl_binary = '/usr/bin/openssl';
my $xdelta_binary  = '/usr/bin/xdelta';

my $serialport          = $ENV{'SERIAL_PORT'}         || '/dev/ttyUSB0';
my $crt_dir             = $ENV{'CRT_DIRECTORY'}       || '../crt';
my $crl_dir             = $ENV{'CRL_DIRECTORY'}       || '../www';
my $smtp_host           = $ENV{'SMTP_HOST'}           || 'localhost';
my $smtp_port           = $ENV{'SMTP_PORT'}           || '25';
my $smtp_helo_name      = $ENV{'SMTP_HELO_NAME'}      || 'hlin.cacert.org';
my $smtp_return_address = $ENV{'SMTP_RETURN_ADDRESS'} || 'returns@cacert.org';
my $smtp_x_mailer       = $ENV{'SMTP_X_MAILER'}       || 'CAcert.org Website';
my $smtp_errors_to      = $ENV{'SMTP_ERRORS_TO'}      || $smtp_return_address;
my $db_name             = $ENV{'MYSQL_WEBDB_DATABASE'};
my $db_host             = $ENV{'MYSQL_WEBDB_HOSTNAME'};
my $db_user             = $ENV{'MYSQL_WEBDB_USER'};
my $db_password         = $ENV{'MYSQL_WEBDB_PASSWORD'};

my %revoke_file =
    ( 2 => "$crl_dir/class3-revoke.crl", 1 => "$crl_dir/revoke.crl" );

#End of configurations

########################################################

my Device::SerialPort $PortObj;

## constants

# constants for serial interface parameters
Readonly my $DEFAULT_BAUD_RATE => 115_200;
Readonly my $DEFAULT_DATA_BITS => 8;
Readonly my $DEFAULT_STOP_BITS => 1;

# constants related to assurance points and certificate validity
Readonly my $MINIMUM_POINTS_FOR_ASSURED_MEMBER => 50;
Readonly my $VALIDITY_DAYS_SERVER_ASSURED      => 730;
Readonly my $VALIDITY_DAYS_SERVER_WOT          => 180;

# constants for mail templates
Readonly my $ACCOUNT_BASE_URL => 'https://www.cacert.org/account.php';
Readonly my %ACCOUNT_PAGE_ID  => { server => 15, client => 6 };
Readonly my $ROOT_CERTIFICATE_DOWNLOAD_URL =>
    'https://www.cacert.org/index.php?id=3';
Readonly my %ROOT_CERT_FINGERPRINT => {
    md5  => 'A6:1B:37:5E:39:0D:9C:36:54:EE:BD:20:31:46:1F:6B',
    sha1 => '135C EC36 F49C B8E9 3B1A B270 CD80 8846 76CE 8F33',
};
Readonly my $OPENPGP_KEY_ID =>
    'pub 1024D/65D0FD58 2003-07-11 CA Cert Signing Authority (Root CA) <gpg@cacert.org>';
Readonly my $OPENPGP_FINGERPRINT =>
    'Key fingerprint = A31D 4F81 EF4E BD07 B456 FA04 D2BB 0D01 65D0 FD58';
Readonly my $EMAIL_SUBJECT_TEMPLATE => '[CAcert.org] %s';
Readonly my $EMAIL_FROM_ADDRESS     => 'support@cacert.org';
Readonly my $EMAIL_FROM_NAME        => 'CAcert Support';

# protocol related constants
Readonly my $PROTOCOL_VERSION              => 1;
Readonly my $MAX_TRIES                     => 10_000;
Readonly my $WAIT_FOR_INITIAL_DATA_SECONDS => 120;
Readonly my $WAIT_FOR_HANDSHAKE_SECONDS    => 20;
Readonly my $WAIT_FOR_ACK_SECONDS          => 5;
Readonly my $DEFAULT_MTU                   => 30;
Readonly my $START_BYTE                    => chr 0x02;
Readonly my $ACK_BYTE                      => chr 0x10;
Readonly my $RESET_BYTE                    => chr 0x11;
Readonly my $ZERO_LENGTH_FIELD             => "\N{NULL}\N{NULL}\N{NULL}";
Readonly my $MAX_BLOCK_SIZE                => 2**24;
Readonly my $MAGIC_BYTES                   => 'rie4Ech7';
Readonly my $READ_BLOCK_SIZE               => 100;
Readonly my $MAGIC_BYTES_LENGTH            => length $MAGIC_BYTES;
Readonly my $CRC_LENGTH                    => 1;
Readonly my $LENGTH_FIELD_SIZE             => 3;
Readonly my $TRAILING_BYTES_SIZE => $CRC_LENGTH + $MAGIC_BYTES_LENGTH;

Readonly::Hash my %REQUEST_TYPES => { NUL => 0, SIGN => 1, REVOKE => 2 };
Readonly::Hash my %MD_ALGORITHMS => {
    'md5'    => 1,
    'sha1'   => 2,
    'rmd160' => 3,
    'sha256' => 8,
    'sha384' => 9,
    'sha512' => 10,
};
Readonly::Hash my %IDENTITY_SYSTEMS => {
    X509    => 1,
    OPENPGP => 2,
};

Readonly::Hash my %MONTH_NUMBERS => {
    'Jan' => 1,
    'Feb' => 2,
    'Mar' => 3,
    'Apr' => 4,
    'May' => 5,
    'Jun' => 6,
    'Jul' => 7,
    'Aug' => 8,
    'Sep' => 9,
    'Oct' => 10,
    'Nov' => 11,
    'Dec' => 12,
};

Readonly::Hash my %CERT_PROFILES => {
    client         => 0,     #   "0"=>"client.cnf",
    org_client     => 1,     #   "1"=>"client-org.cnf",
    codesign       => 2,     #   "2"=>"client-codesign.cnf",
    client_machine => 3,     #   "3"=>"client-machine.cnf",
    client_ads     => 4,     #   "4"=>"client-ads.cnf",
    server         => 5,     #   "5"=>"server.cnf",
    org_server     => 6,     #   "6"=>"server-org.cnf",
    xmpp_server    => 7,     #   "7"=>"server-jabber.cnf",
    ocsp           => 8,     #   "8"=>"server-ocsp.cnf",
    timestamp      => 9,     #   "9"=>"server-timestamp.cnf",
    proxy          => 10,    #   "10"=>"proxy.cnf",
    sub_ca         => 11,    #   "11"=>"subca.cnf"
};

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

sub write_file {
    my ( $file_name, $content ) = @_;
    open my $OUT, '>',
        $file_name
        or log_error_and_die( sprintf 'could not open %s for writing: %s',
        $file_name, $OS_ERROR );
    print {$OUT} $content
        or log_error_and_die( sprintf 'could not write to %s: %s',
        $file_name, $OS_ERROR );
    close $OUT
        or log_error_and_die( sprintf 'could not close %s: %s',
        $file_name, $OS_ERROR );
    return;
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

foreach ( keys %revoke_file ) {
    if ( !-f $revoke_file{$_} ) {
        next;
    }
    my $revoke_hash = sha1_hex( read_file( $revoke_file{$_} ) );
    sys_log("Root $_: Hash $revoke_file{$_} = $revoke_hash\n");
}

sub trim {
    my ($str) = @_;
    $str =~ s/^\s+|\s+$//gxms;
    return $str;
}

sub add_slashes {
    my ($str) = @_;
    $str =~ s/['"\\]/\\$1/gxms;
    return ($str);
}

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

sys_log("Opening serial interface:\n");

#We have to open the SerialPort and close it again, so that we can bind it to a Handle
$PortObj = Device::SerialPort->new($serialport);
serial_port_settings($PortObj);
$PortObj->save('serial.conf');

undef $PortObj;

$PortObj = tie( *SER, 'Device::SerialPort', 'serial.conf' )
    || log_error_and_die(
    "Can't tie using Configuration_File_Name: $OS_ERROR");

if ( !defined $PortObj ) {
    log_error_and_die('Could not open Serial Interface!');
}
serial_port_settings($PortObj);

sys_log("Serial interface opened: $PortObj\n");

my $sel = IO::Select->new( \*SER );

my $dbh =
    DBI->connect( "DBI:mysql:$db_name:$db_host", $db_user, $db_password,
    { RaiseError => 1, AutoCommit => 1 } )
    || log_error_and_die('Error establishing the database connection.');

sub mysql_query {
    my ($query) = @_;
    $dbh->do($query);
    return;
}

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
            $len, length $data, ( length($data) - $LENGTH_FIELD_SIZE ) );
    }
    if ( length($data) - $LENGTH_FIELD_SIZE != $len ) {
        return;
    }
    return substr $data, $LENGTH_FIELD_SIZE;
}

# unpack3array extracts a whole array of concatenated packed data.
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

# Raw send function over the Serial Interface  (+debugging)
sub send_data {
    my ($bytes) = @_;
    if ( !defined $bytes ) {
        return;
    }
    if ( $debug >= 1 ) {
        sys_log( sprintf "Sending %d bytes\n", length $bytes );
    }
    if ( $debug >= 2 ) {
        sys_log( sprintf "Bytes to send: %s\n", hexdump($bytes) );
    }
    my $data  = $bytes;
    my $total = 0;
    while ( length $data ) {
        my $bytes_written =
            scalar( $PortObj->write( substr $data, 0, $DEFAULT_MTU ) ) || 0;
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

#Send data over the Serial Interface with handshaking:
sub send_handshaked {
    my ($bytes) = @_;
    if ( $debug >= 1 ) {
        sys_log("Shaking hands ...\n");
    }
    send_data($START_BYTE);

    if ( !scalar( $sel->can_read($WAIT_FOR_HANDSHAKE_SECONDS) ) ) {
        log_error_and_die('Handshake uncompleted. Connection lost!');
    }
    my $data   = q{};
    my $length = read SER, $data, 1;
    if ( $length && $data eq $ACK_BYTE ) {
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
                    sys_log("Sent successfully! ...\n");
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
        log_error_and_die("!Cannot send! $length $data! Stopped sending.");
    }
    return;
}

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

        while ( $block_finished == 0 ) {
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
            $block_finished = defined( unpack3 substr $block,
                0, -( $MAGIC_BYTES_LENGTH + $CRC_LENGTH ) ) ? 1 : 0;

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
        }
        if ( $debug >= 2 ) {
            sys_log( sprintf "Block done: %s\n", hexdump($block) );
        }
        send_data($ACK_BYTE);
        return ($block);
    }
    else {
        if ( length($data) == 0 ) {
            log_error_and_die('Error: no answer received, timeout.');
        }
        log_error_and_die( sprintf 'Error: wrong start byte: %s',
            hexdump($data) );
    }

    sys_log("Waiting for next request ...\n");
    return;
}

# @result(Version,Action,Errorcode,Response)=Request(Version=1,Action=1,System=1,Root=1,Configuration="...",Parameter="...",Request="...");
sub send_request {
    my ( $version, $request_type, $arg_ref ) = @_;

    my $id_system = exists $arg_ref->{id_system} ? $arg_ref->{id_system} : 0;
    my $root      = exists $arg_ref->{root}      ? $arg_ref->{root}      : 0;
    my $profile   = exists $arg_ref->{profile}   ? $arg_ref->{profile}   : 0;
    my $md_algorithm =
        exists $arg_ref->{md_algorithm} ? $arg_ref->{md_algorithm} : 0;
    my $days    = exists $arg_ref->{days}    ? $arg_ref->{days}    : 0;
    my $spkac   = exists $arg_ref->{spkac}   ? $arg_ref->{spkac}   : 0;
    my $content = exists $arg_ref->{content} ? $arg_ref->{content} : q{};
    my $san     = exists $arg_ref->{san}     ? $arg_ref->{san}     : q{};
    my $subject = exists $arg_ref->{subject} ? $arg_ref->{subject} : q{};

    if ( $debug >= 2 ) {
        sys_log(  "Sending request:\n"
                . "  Version: $version\n"
                . "  Action: $request_type\n"
                . "  System: $id_system\nRoot: $root\nConfig: $profile\n"
                . "  MD algorithm: $md_algorithm\n"
                . "  Days: $days\n"
                . "  SPKAC: $spkac\n"
                . "  Content: $content\n"
                . "  SAN: $san\n"
                . "  Subject: $subject\n" );
    }

    if ( $root < 0 ) {
        $root = 0;
    }
    send_handshaked(
        pack3(
            pack3(
                pack 'CCCCCCnC', $version, $request_type,
                $id_system,      $root,    $profile,
                $md_algorithm,   $days,    $spkac
                )
                . pack3($content)
                . pack3($san)
                . pack3($subject)
        )
    );
    my $data   = receive_block();
    my @fields = unpack3array( substr $data, $LENGTH_FIELD_SIZE,
        -$TRAILING_BYTES_SIZE );

    if ( $debug >= 2 ) {
        sys_log( sprintf "Answer from Server: %s\n", hexdump($data) );
    }

# fields has header, content and 2 optional arguments. We are interested in the content
    return $fields[1];
}

sub calculate_validity_days {
    my ($member_id) = @_;
    if ( $member_id != 0 ) {
        my @sum = $dbh->selectrow_array(
            sprintf
                q{SELECT SUM(points) AS total FROM notary WHERE `to` = '%s' AND deleted = 0 GROUP BY `to`},
            $member_id
        );
        if ( $debug >= 1 ) {
            sys_log( printf "sum of points for member %d: %d\n",
                $member_id, $sum[0] );
        }

        return ( $sum[0] >= $MINIMUM_POINTS_FOR_ASSURED_MEMBER )
            ? $VALIDITY_DAYS_SERVER_ASSURED
            : $VALIDITY_DAYS_SERVER_WOT;
    }
    return $VALIDITY_DAYS_SERVER_WOT;
}

sub x509_extract_subject_altnames {
    my ($subject_dn) = @_;

# FIXME: handling subject DN as literal string is wrong. This causes bugs like https://bugs.cacert.org/view.php?id=996
# We need a proper ASN.1 parser to parse these correctly
# Requested SANs should be a separate field and not be stored in the Subject DN
    my @dn_parts       = split qr{/}xms, $subject_dn;
    my $SAN            = q{};
    my $new_subject_dn = q{};
    foreach my $val (@dn_parts) {
        my @bit = split qr/=/xms, $val;
        if ( $bit[0] eq 'subjectAltName' ) {
            if ( $SAN ne q{} ) {
                $SAN .= q{,};
            }
            $SAN .= trim( $bit[1] );
        }
        else {
            $new_subject_dn .= q{/} . $val;
        }
    }
    $new_subject_dn =~ s{^//}{/}xms;
    $new_subject_dn =~ s/[\t\r\n\x00"\\']//gxms;
    $SAN            =~ s/[\s\x00"\\']//gxms;
    return ( $SAN, $new_subject_dn );
}

sub parse_openssl_date {
    my ( $date_str, $label ) = @_;

    # certificate timestamps are always expressed as GMT dates (see RFC-5280
    # https://tools.ietf.org/html/rfc5280#section-4.1.2.5)
    #
    # Example: notAfter=Aug  8 10:26:34 2007 GMT
    if ($date_str =~ m{
        $label                       # start of openssl date output
        (\w{2,4})[ ]*                # month name
        (\d{1,2})[ ]*                # day of month
        (\d{1,2}:\d{1,2}:\d{1,2})[ ] # time
        (\d{4})[ ]                   # year
        GMT                          # timezone is always GMT
        }xms
        )
    {
        return "$4-" . $MONTH_NUMBERS{$1} . "-$2 $3";
    }
    return;
}

sub x509_extract_expiry_date {
    my ($certificate_filename) = @_;

    my $stdout = IO::Handle->new();
    my $pid = open3( undef, $stdout, $stdout, $openssl_binary, 'x509', '-in',
        $certificate_filename, '-noout', '-enddate' );
    my $data = q{};
    {
        local $INPUT_RECORD_SEPARATOR = undef;
        $data = <$stdout>;
    }
    waitpid $pid, 0;

    if ( my $date = parse_openssl_date( $data, qr/notAfter=/xms ) ) {
        if ( $debug >= 1 ) {
            sys_log("Expiry date found: $date\n");
        }
        return $date;
    }
    sys_log("Expiry date not found: $data\n");
    return q{};
}

sub crl_up_to_date {
    my ($crl_filename) = @_;

    if ( !-f $crl_filename ) {
        return;
    }
    my $stdout = IO::Handle->new();
    my $pid    = open3(
        undef,         $stdout,   $stdout,       $openssl_binary,
        'crl',         '-in',     $crl_filename, '-noout',
        '-lastupdate', '-inform', 'der'
    );
    my $data = q{};
    {
        local $INPUT_RECORD_SEPARATOR = undef;
        $data = <$stdout>;
    }
    waitpid $pid, 0;
    sys_log("CRL: $data");

    if ( my $date = parse_openssl_date( $data, qr/lastUpdate=/xms ) ) {
        if ( $debug >= 1 ) {
            sys_log("CRL issuing date found: $date\n");
        }
        my $compare = strftime '%Y-%m-%d', gmtime;
        if ( $debug >= 1 ) {
            sys_log("Comparing $date with $compare\n");
        }
        return substr( $date, 0, length $compare ) eq $compare;
    }
    sys_log(
        "Expiry date not found. Perhaps DER format is necessary? Hint: $data\n"
    );
    return;
}

sub x509_extract_serial_number {
    my ($certificate_filename) = @_;

    my $data =
        run_openssl_command( 'x509', '-in', $certificate_filename, '-noout',
        '-serial' );
    if ( $data =~ m/serial=([[:xdigit:]]+)/xms ) {
        return $1;
    }
    return q{};
}

Readonly my $SECONDS_IN_MINUTE      => 60;
Readonly my $SECONDS_IN_HOUR        => 60 * $SECONDS_IN_MINUTE;
Readonly my $SECONDS_IN_DAY         => 24 * $SECONDS_IN_HOUR;
Readonly my $SECONDS_IN_YEAR        => 365 * $SECONDS_IN_DAY;
Readonly my $WAIT_SYSTEM_ERROR_MASK => 8;

sub openpgp_extract_expiry_date {
    my ($public_key_file) = @_;

    my $result = q{};
    my $cts    = 0;

    my ( $output, $error ) = ( IO::Handle->new(), IO::Handle->new() );
    my $pid =
        open3( undef, $output, $error, $gpg_binary, '--list-packets',
        $public_key_file );
    waitpid $pid, 0;
    if ( ( $CHILD_ERROR >> $WAIT_SYSTEM_ERROR_MASK ) != 0 ) {
        log_error_and_die(
            "command $gpg_binary -vv $public_key_file failed: $CHILD_ERROR <$error>"
        );
    }

    local $INPUT_RECORD_SEPARATOR = "\n";
    while (<$output>) {
        if ( $debug >= 1 ) {
            sys_log("$_");
        }
        if (m/^\s*version[ ]\d+,[ ]created[ ](\d+),[ ]md5len[ ]0,[ ]sigclass[ ](?:0x[[:xdigit:]]+|\d+)\s*$/xms
            )
        {
            if ( $debug >= 1 ) {
                sys_log("Detected CTS: $1\n");
            }
            $cts = int $1;
        }
        elsif (
            m{
                ^\s*
                critical[ ]hashed[ ]subpkt[ ]\d+[ ]len[ ]\d+[ ]
                \(
                sig[ ]expires[ ]after[ ]
                (?:(\d+)y)?
                (?:(\d+)d)?
                (?:(\d+)h)?
                (\d+)m
                \)
                \s*$}xms
            )
        {
            if ( $debug >= 1 ) {
                sys_log("Detected FRAME $1 $2 $3 $4\n");
            }
            $cts += $1 * $SECONDS_IN_YEAR;
            $cts += $2 * $SECONDS_IN_DAY;
            $cts += $3 * $SECONDS_IN_HOUR;
            $cts += $4 * $SECONDS_IN_MINUTE;
            $result = $cts;
            last;
        }
    }

    if ( $debug >= 1 ) {
        sys_log("CTS: $cts  R: $result\n");
    }
    if ( !( $result eq q{} ) ) {
        return strftime '%Y-%m-%d %H:%M:%S', gmtime $result;
    }
    if ( $debug >= 1 ) {
        sys_log("$result\n");
    }
    return $result;
}

Readonly my $DEFAULT_LANGUAGE => 'en_US';

# Sets the locale according to the users preferred language
sub get_user_language {
    my ($language) = @_;

    return $language eq q{} ? $DEFAULT_LANGUAGE : $language;
}

sub get_user_data {
    my ($user_id) = @_;
    my $sth = $dbh->prepare(q{SELECT * FROM users WHERE id=?});
    $sth->bind_param( 1, $user_id );
    $sth->execute();
    while ( my $row_data = $sth->fetchrow_hashref() ) {
        return %{$row_data};
    }
    return ();
}

sub _ {
    my ($text) = @_;

    return gettext($text);
}

sub sendmail {
    my ( $to, $subject, $body, $from, $reply_to, $to_name, $from_name ) = @_;

    my $email = Email::MIME->create(
        header_str => [
            From => $from_name eq q{}
            ? $from
            : sprintf( '%s <%s>', $from_name, $from ),
            To => $to_name eq q{} ? $to : sprintf( '%s <%s>', $to_name, $to ),
            Subject => trim($subject),
            Sender  => $smtp_errors_to,
        ],
        body => $body
    );
    $email->header_set( 'X-Mailer',  $smtp_x_mailer );
    $email->header_set( 'Errors-To', $smtp_errors_to );
    if ( $reply_to ne q{} ) {
        $email->header_set( 'Reply-To', $reply_to );
    }

    my $smtp = Net::SMTP->new(
        $smtp_host,
        Port  => $smtp_port,
        Debug => ( $debug >= 1 ) ? 1 : 0,
        Hello => $smtp_helo_name
    );
    $smtp->mail($smtp_return_address);
    $smtp->recipient($to);
    $smtp->data( $email->as_string );
    $smtp->quit();
}

Readonly::Hash my %SQL_REQUESTED_CERTS => {
    domaincerts => <<'SQL',
SELECT d.id, d.type, d.subject, d.csr_name, d.md, d.`CN`, d2.memid
FROM domaincerts d
         JOIN domains d2 ON d2.id = d.domid
WHERE d.crt_name = '' AND d.csr_name != '' AND warning < 3
SQL
    emailcerts =>
        q{SELECT * FROM emailcerts WHERE crt_name = '' AND csr_name != '' AND warning < 3},
    orgdomaincerts => <<'SQL',
SELECT d.id, d.type, d.subject, d.csr_name, d.md, d.`CN`, o.memid
FROM orgdomaincerts d
         JOIN org o ON d.orgid = o.orgid
WHERE d.crt_name = '' AND d.csr_name != '' AND d.warning < 3
SQL
    orgemailcerts =>
        q{SELECT * FROM orgemailcerts WHERE crt_name = '' AND csr_name != '' AND warning < 3},
};
Readonly::Hash my %SQL_UPDATE_CERT => {
    domaincerts =>
        q{UPDATE domaincerts SET crt_name=?, modified=CURRENT_TIMESTAMP, serial=?, expire=? WHERE id = ?},
    emailcerts =>
        q{UPDATE emailcerts SET crt_name=?, modified=CURRENT_TIMESTAMP, serial=?, expire=? WHERE id = ?},
    orgdomaincerts =>
        q{UPDATE orgdomaincerts SET crt_name=?, modified=CURRENT_TIMESTAMP, serial=?, expire=? WHERE id = ?},
    orgemailcerts =>
        q{UPDATE orgemailcerts SET crt_name=?, modified=CURRENT_TIMESTAMP, serial=?, expire=? WHERE id = ?},
};
Readonly::Hash my %SQL_INCREMENT_WARNING_CERT => {
    domaincerts => q{UPDATE domaincerts SET warning=warning + 1 WHERE id = ?},
    emailcerts  => q{UPDATE emailcerts SET warning=warning + 1 WHERE id = ?},
    orgdomaincerts =>
        q{UPDATE orgdomaincerts SET warning=warning + 1 WHERE id = ?},
    orgemailcerts =>
        q{UPDATE orgemailcerts SET warning=warning + 1 WHERE id = ?},
};

Readonly my $PATH_SPLIT_FACTOR => 1_000;
Readonly my $DIRECTORY_MODE    => oct 777;
Readonly my $ONE_YEAR          => 365;
Readonly my $TWO_YEARS         => $ONE_YEAR * 2;

sub x509_decide_profile {
    my ( $type, $is_org, $is_server, $is_codesign ) = @_;

    if ( $type =~ m/^[89]$/xms ) {
        return $type;
    }
    if ( $is_org == 1 ) {
        if ( $is_codesign == 1 ) {

            # TODO: define separate profile for organization code signing
            return $CERT_PROFILES{codesign};
        }
        if ( $is_server == 1 ) {
            return $CERT_PROFILES{org_server};
        }
        return $CERT_PROFILES{org_client};
    }
    if ( $is_codesign == 1 ) {
        return $CERT_PROFILES{codesign};
    }
    if ( $is_server == 1 ) {
        return $CERT_PROFILES{server};
    }
    return $CERT_PROFILES{client};
}

sub x509_save_certificate_pem {
    my ( $crt, $crt_name ) = @_;

    if ( length $crt ) {
        if ( $crt =~ m/^-----BEGIN[ ]CERTIFICATE-----/xms ) {
            write_file( $crt_name, $crt );
        }
        else {
            my $der_certificate = "$crt_name.der";
            write_file($der_certificate);
            run_openssl_command( 'x509', '-in', $der_certificate, '-inform',
                'der', '-out', $crt_name );
        }
    }
    else {
        sys_log("ZERO Length certificate received.\n");
    }
    return;
}

sub x509_issue_certificate {
    my ( $is_org, $is_server, $row ) = @_;

    my $cert_id        = $row->{id};
    my $csr_name       = $row->{csr_name};
    my $member_id      = exists $row->{memid} ? $row->{memid} : undef;
    my $cert_type      = $row->{type};
    my $is_codesign    = $row->{codesign};
    my $subject        = $row->{subject};
    my $message_digest = $row->{'md'};
    my $root_cert_id   = $row->{'rootcert'} - 1;
    my $is_spkac       = $row->{'keytype'} eq 'NS' ? 1 : 0;

    my $prefix = sprintf '%s%s', $is_org ? 'org' : q{},
        $is_server ? 'server' : 'client';
    my $table = sprintf '%s%s', $is_org ? 'org' : q{},
        $is_server ? 'domaincerts' : 'emailcerts';
    my $short    = int( $cert_id / $PATH_SPLIT_FACTOR );
    my $crt_name = sprintf '%s/%s/%s/%s-%d.crt', $crt_dir, $prefix, $short,
        $prefix, $cert_id;

    my $certificate_directory = dirname($crt_name);
    mkdir $certificate_directory, $DIRECTORY_MODE;
    sys_log("New Layout: $crt_name\n");

    my $profile =
        x509_decide_profile( $cert_type, $is_org, $is_server, $is_codesign );

    sys_log("Opening $csr_name\n");
    my $content = read_file($csr_name);

    if ( $debug >= 1 ) {
        sys_log("Read $csr_name.\n");
        sys_log("Subject: --$subject--\n");
    }

    my $SAN;
    ( $SAN, $subject ) = x509_extract_subject_altnames($subject);
    if ( $debug >= 1 ) {
        sys_log("Subject: --$subject--\n");
        sys_log("SAN: --$SAN--\n");
        sys_log("memid: $member_id\n");
    }

    my $days =
        $is_org
        ? ( $is_server ? ($TWO_YEARS) : $ONE_YEAR )
        : calculate_validity_days($member_id);

    my $md_id =
        exists $MD_ALGORITHMS{$message_digest}
        ? $MD_ALGORITHMS{$message_digest}
        : 0;

    my $crt = send_request(
        $PROTOCOL_VERSION,
        $REQUEST_TYPES{SIGN},
        {   id_system    => $IDENTITY_SYSTEMS{X509},
            root         => $root_cert_id,
            profile      => $profile,
            md_algorithm => $md_id,
            days         => $days,
            spkac        => $is_spkac,
            content      => $content,
            san          => $SAN,
            subject      => $subject,
        }
    );

    x509_save_certificate_pem( $crt, $crt_name );

    if ( !-s $crt_name ) {
        sys_log( sprintf "Could not find the issued certificate. %s %d\n",
            $crt_name, $cert_id );
        my $sth = $dbh->prepare( $SQL_INCREMENT_WARNING_CERT{$table} );
        $sth->execute($cert_id);
        return;
    }
    sys_log("Opening $crt_name\n");

    my $expiry_date = x509_extract_expiry_date($crt_name);
    my $serial      = x509_extract_serial_number($crt_name);

    my %user = get_user_data($member_id);
    my $lang = get_user_language( $user{language} );
    local $ENV{'LANG'} = $lang;
    setlocale( LC_ALL, $lang );

    foreach ( sort keys %user ) {
        if ( $debug >= 1 ) {
            sys_log("  $_ -> $user{$_}\n");
        }
    }

    my $sth = $dbh->prepare( $SQL_UPDATE_CERT{$table} );
    $sth->execute( $crt_name, $serial, $expiry_date, $cert_id );

    my $body        = sprintf _('Hi %s,') . "\n\n", $user{fname};
    my $email       = exists $row->{email} ? $row->{email} : q{};
    my $common_name = $row->{'CN'};
    $body
        .= sprintf _(
        'You can collect your certificate for %s by going to the following location:'
        )
        . "\n\n",
        $email . $common_name;
    $body .= sprintf "%s?id=%d&cert=%d\n\n",
        $ACCOUNT_BASE_URL,
        $is_server ? $ACCOUNT_PAGE_ID{server} : $ACCOUNT_PAGE_ID{client},
        $cert_id;
    $body
        .= _(
        q{If you have not imported CAcert's root certificate yet, please go to:}
        ) . "\n\n";
    $body .= sprintf "%s\n\n", $ROOT_CERTIFICATE_DOWNLOAD_URL;
    $body .= sprintf "Root cert fingerprint = %s\n",
        $ROOT_CERT_FINGERPRINT{md5};
    $body .= sprintf "Root cert fingerprint = %s\n\n\n",
        $ROOT_CERT_FINGERPRINT{sha1};
    $body .= _('Best regards') . "\n" . _('CAcert.org Support!') . "\n\n";
    sys_log($body);
    sendmail( $user{email},
        sprintf( $EMAIL_SUBJECT_TEMPLATE, _('Your certificate') ),
        $body, $EMAIL_FROM_ADDRESS, q{}, q{}, $EMAIL_FROM_NAME );
    return;
}

sub x509_handle_certificates {
    my ( $is_org, $is_server ) = @_;
    my $org = $is_org ? 'org' : q{};

    my $table = $org . ( $is_server ? 'domaincerts' : 'emailcerts' );

    sys_log("HandleCerts $table\n");

    my $query = $SQL_REQUESTED_CERTS{$table};
    if ( $debug >= 1 ) {
        sys_log("$query\n");
    }
    my $sth = $dbh->prepare($query);
    $sth->execute();
    while ( my $row_data = $sth->fetchrow_hashref() ) {
        x509_issue_certificate( $is_org, $is_server, $row_data );
    }
    return;
}

sub run_openssl_command {
    my @args = @_;

    my $stdout = IO::Handle->new();
    my $output;
    my $pid = open3( undef, $stdout, $stdout, $openssl_binary, @args );
    {
        local $INPUT_RECORD_SEPARATOR = undef;
        $output = <$stdout>;
    }
    waitpid $pid, 0;
    if ( ( $CHILD_ERROR >> $WAIT_SYSTEM_ERROR_MASK ) != 0 ) {
        log_error_and_die( sprintf 'command failed: %s %s -> %s',
            $openssl_binary, join( q{ }, @args ), $CHILD_ERROR );
    }
    if ( $debug >= 1 ) {
        sys_log( sprintf "command %s %s output: %s\n",
            $openssl_binary, join( q{ }, @args ), $output );
    }
    return $output;
}

sub run_xdelta_command {
    my @args = @_;

    my $stdout = IO::Handle->new();
    my $output;
    my $pid = open3( undef, $stdout, $stdout, $xdelta_binary, @args );
    {
        local $INPUT_RECORD_SEPARATOR = undef;
        $output = <$stdout>;
    }
    waitpid $pid, 0;
    if ( ( $CHILD_ERROR >> $WAIT_SYSTEM_ERROR_MASK ) != 0 ) {
        log_error_and_die( sprintf 'command failed: %s %s -> %s',
            $xdelta_binary, join( q{ }, @args ), $CHILD_ERROR );
    }
    if ( $debug >= 1 ) {
        sys_log( sprintf "command %s %s output: %s\n",
            $xdelta_binary, join( q{ }, @args ), $output );
    }
    return $output;
}

sub x509_refresh_crl {
    my ( $crl, $crl_name ) = @_;

    my $crl_directory = dirname($crl_name);
    if ( !-d $crl_directory ) {
        mkdir $crl_directory;
    }

    my $command;
    my $output;

    if ( length $crl ) {
        my $temporary_crl = "$crl_name.tmp";
        my $crl_patch     = "$crl_name.patch";

        if ($debug >= 2) {
            sys_log(sprintf "received crl\n%s\n", hexdump($crl));
        }

        if ( $crl =~ m/^-----BEGIN[ ]X509[ ]CRL-----/xms ) {
            my $crl_filename = "$crl_name.pem";
            write_file( $crl_filename, $crl );

            run_openssl_command( 'crl', '-in', $crl_filename, '-outform',
                'der', '-out', $temporary_crl );
        }
        else {
            write_file( $crl_patch, $crl );

            $command = "xdelta patch $crl_patch $crl_name $crl_patch.tmp";
            $output  = run_xdelta_command( 'patch', $crl_patch, $crl_name,
                $temporary_crl );
        }

        my $stdout = IO::Handle->new();
        my $pid    = open3(
            undef,     $stdout,   $stdout, $openssl_binary,
            'crl',     '-verify', '-in',   $temporary_crl,
            '-inform', 'der',     '-noout'
        );
        waitpid $pid, 0;

        {
            local $INPUT_RECORD_SEPARATOR = undef;
            $output = <$stdout>;
        }
        if ( $debug >= 1 ) {
            sys_log( "crl verify command output for %s: %s\n",
                $temporary_crl, $output );
        }
        if ( ( $CHILD_ERROR >> $WAIT_SYSTEM_ERROR_MASK ) == 0 ) {
            rename $temporary_crl, "$crl_name";
            return 1;
        }
        else {
            sys_log(
                "VERIFICATION OF NEW CRL DID NOT SUCCEED! PLEASE REPAIR!\n");
            sys_log("Broken CRL is available as $temporary_crl\n");
        }
    }
    else {
        sys_log("RECEIVED AN EMPTY CRL!\n");
    }
    return 0;
}

sub x509_refresh_crls {
    foreach my $root_certificate ( keys %revoke_file ) {
        if ( !crl_up_to_date( $revoke_file{$root_certificate} ) ) {
            sys_log("Update of the CRL $root_certificate is necessary!\n");
            my $crl_name = $revoke_file{$root_certificate};
            my $revoke_hash;
            if ( -f $crl_name ) {
                $revoke_hash = sha1_hex( read_file($crl_name) );
            }
            else {
                $revoke_hash = sha1_hex(q{});
            }
            my $crl = send_request(
                $PROTOCOL_VERSION,
                $REQUEST_TYPES{REVOKE},
                {   id_system => $IDENTITY_SYSTEMS{X509},
                    root      => $root_certificate - 1,
                    days      => 365,
                    subject   => $revoke_hash
                }
            );
            if ( $debug >= 2 ) {
                sys_log( sprintf "Received %d %s\n",
                    length $crl, hexdump($crl) );
            }

            x509_refresh_crl( $crl, $crl_name );
        }
    }
    return;
}

Readonly::Hash my %SQL_FIND_REVOKED_CERTS => {
    domaincerts =>
        q{SELECT d.*, d2.memid FROM domaincerts d JOIN domains d2 ON d2.id=d.domid WHERE d.revoked='1970-01-01 10:00:01'},
    emailcerts =>
        q{SELECT * FROM emailcerts WHERE revoked='1970-01-01 10:00:01'},
    orgdomaincerts =>
        q{SELECT d.*, o.memid FROM orgdomaincerts d JOIN org o ON d.orgid = o.orgid WHERE d.revoked='1970-01-01 10:00:01'},
    orgemailcerts =>
        q{SELECT * FROM orgemailcerts WHERE revoked='1970-01-01 10:00:01'},
};
Readonly::Hash my %SQL_UPDATE_REVOKED_CERT => {
    domaincerts =>
        q{UPDATE domaincerts SET revoked=CURRENT_TIMESTAMP WHERE id=?},
    emailcerts =>
        q{UPDATE emailcerts SET revoked=CURRENT_TIMESTAMP WHERE id=?},
    orgdomaincerts =>
        q{UPDATE orgdomaincerts SET revoked=CURRENT_TIMESTAMP WHERE id=?},
    orgemailcerts =>
        q{UPDATE orgemailcerts SET revoked=CURRENT_TIMESTAMP WHERE id=?},
};

sub revoke_certificates {
    my ( $is_org, $is_server ) = @_;
    my $org = $is_org ? 'org' : q{};

    my $table = $org . ( $is_server ? 'domaincerts' : 'emailcerts' );

    my $sth = $dbh->prepare( $SQL_FIND_REVOKED_CERTS{$table} );
    $sth->execute();
    while ( my $row_data = $sth->fetchrow_hashref() ) {
        my %row = %{$row_data};

        my $prefix = $org . ( $is_server ? 'server' : 'client' );
        my $short  = int( $row{'id'} / $PATH_SPLIT_FACTOR );

        my $crt_name = sprintf '%s/%s/%s/%s-%d.crt', $crt_dir, $prefix,
            $short, $prefix, $row{'id'};
        my $crl_name = $revoke_file{ $row{'rootcert'} };

        my $content = read_file($crt_name);

        my $revoke_hash = sha1_hex( read_file($crl_name) );

        my $crl = send_request(
            $PROTOCOL_VERSION,
            $REQUEST_TYPES{REVOKE},
            {   id_system => $IDENTITY_SYSTEMS{X509},
                root      => $row{'rootcert'} - 1,
                days      => 365,
                content   => $content,
                subject   => $revoke_hash,
            }
        );
        my $result = x509_refresh_crl( $crl, $crl_name );

        if ( $result == 1 ) {
            $dbh->do( sprintf $SQL_UPDATE_REVOKED_CERT{$table},
                int $row{'id'} );

            if ( $is_org == 0 ) {
                if ( $is_server == 1 ) {
                    my @a = $dbh->selectrow_array(
                        sprintf q{SELECT memid FROM domains WHERE id='%d'},
                        int $row{domid} );
                    send_revoke_mail( $a[0], $row{'CN'}, $row{'serial'} );
                }
                else {
                    send_revoke_mail( $row{memid}, $row{'CN'},
                        $row{'serial'} );
                }
            }
            else {
                my $org_sth = $dbh->prepare(
                    sprintf q{SELECT memid FROM org WHERE orgid='%d'},
                    int $row{orgid} );
                $org_sth->execute();
                while ( my ($member_id) = $org_sth->fetchrow_array() ) {
                    send_revoke_mail( $member_id, $row{'CN'},
                        $row{'serial'} );
                }
            }
        }
    }
    return;
}

sub send_revoke_mail {
    my ( $member_id, $certificate_name, $serial ) = @_;

    my %user = get_user_data($member_id);
    my $lang = get_user_language( $user{language} );
    local $ENV{'LANG'} = $lang;
    setlocale( LC_ALL, $lang );

    my $body = sprintf _('Hi %s') . "\n\n", $user{fname};
    $body
        .= sprintf _(
        q{Your certificate for '%s' with the serial number '%s' has been revoked, as per request.}
        )
        . "\n\n",
        $certificate_name,
        $serial;
    $body .= _('Best regards') . "\n" . _('CAcert.org Support!') . "\n\n";

    if ( $debug >= 1 ) {
        sys_log( sprintf "Sending email to %s\n", $user{email} );
    }
    sendmail( $user{email}, sprintf $EMAIL_SUBJECT_TEMPLATE,
        _('Your certificate'),
        $body, $EMAIL_FROM_ADDRESS, q{}, q{}, $EMAIL_FROM_NAME );
    return;
}

sub openpgp_handle_requests {
    my $sth = $dbh->prepare(q{SELECT * FROM gpg WHERE crt='' AND csr!=''});
    $sth->execute();
    while ( my $row_data = $sth->fetchrow_hashref() ) {
        my %row = %{$row_data};

        my $prefix   = 'gpg';
        my $short    = int( $row{'id'} / $PATH_SPLIT_FACTOR );
        my $csr_name = $row{csr};
        my $crt_name = sprintf '%s/%s/%s/%s-%d.crt',
            $crt_dir, $prefix, $short, $prefix, $row{'id'};

        if ( $debug >= 1 ) {
            sys_log("Opening $csr_name\n");
        }
        my $content = read_file($csr_name);
        if ( $debug >= 1 ) {
            sys_log("Read $csr_name.\n");
        }

        my $crt = send_request(
            $PROTOCOL_VERSION,
            $REQUEST_TYPES{SIGN},
            {   id_system => $IDENTITY_SYSTEMS{OPENPGP},
                root => 0, # hard coded for now, signer could support multiple
                days    => 366,
                content => $content,
            }
        );
        if ( length $crt ) {
            write_file( $crt_name, $crt );
        }

        if ( -s $crt_name ) {
            if ( $debug >= 1 ) {
                sys_log("Opening $crt_name\n");
            }

            my %user = get_user_data( $row{memid} );
            my $lang = get_user_language( $user{language} );
            local $ENV{'LANG'} = $lang;
            setlocale( LC_ALL, $lang );

            my $date       = openpgp_extract_expiry_date($crt_name);
            my $update_sth = $dbh->prepare(
                q{UPDATE gpg SET crt=?, issued=CURRENT_TIMESTAMP, expire=? WHERE id=?}
            );
            $update_sth->execute( $crt_name, $date, $row{'id'} );

            my $body = sprintf _('Hi %s') . "\n\n", $user{fname};
            $body
                .= sprintf _(
                'Your CAcert signed key for %s is available online at:')
                . "\n\n",
                $row{'email'};
            $body .= "https://www.cacert.org/gpg.php?id=3&cert=$row{id}\n\n";
            $body
                .= _(
                q{To help improve the trust of CAcert in general, it's appreciated if you could also sign our key and upload it to a key server. Below is a copy of our primary key details:}
                ) . "\n\n";
            $body .= sprintf "%s\n%s\n\n\n", $OPENPGP_KEY_ID,
                $OPENPGP_FINGERPRINT;
            $body .= _('Best regards') . "\n"
                . _('CAcert.org Support!') . "\n\n";
            sendmail(
                $user{email},
                sprintf( $EMAIL_SUBJECT_TEMPLATE, _('Your OpenPGP Key') ),
                $body,
                $EMAIL_FROM_ADDRESS,
                q{},
                q{},
                $EMAIL_FROM_NAME
            );
        }
        else {
            sys_log( sprintf "Could not find the issued gpg key. %s\n",
                $row{id} );
        }
    }
    return;
}

# Main program loop

my $crlcheck = 0;

local $SIG{INT}  = \&signal_handler;
local $SIG{TERM} = \&signal_handler;

sub signal_handler {
    log_error_and_die("Caught signal $OS_ERROR");
    return;
}

Readonly my $MAINLOOP_SLEEP_MICROSECONDS => 1_700_000;
Readonly my $CRL_CHECK_ITERATIONS        => 100;

while ( -f './client.pl-active' ) {
    sys_log("Signing OpenPGP keys ...\n");
    openpgp_handle_requests();
    sys_log("Issuing certificates ...\n");
    x509_handle_certificates( 0, 0 );    #personal client certs
    x509_handle_certificates( 0, 1 );    #personal server certs
    x509_handle_certificates( 1, 0 );    #org client certs
    x509_handle_certificates( 1, 1 );    #org server certs
    sys_log("Revoking certificates ...\n");
    revoke_certificates( 0, 0 );         #personal client certs
    revoke_certificates( 0, 1 );         #personal server certs
    revoke_certificates( 1, 0 );         #org client certs
    revoke_certificates( 1, 1 );         #org server certs

    $crlcheck++;
    if ( ( $crlcheck % $CRL_CHECK_ITERATIONS ) == 1 ) {
        x509_refresh_crls();
    }

    my $timestamp = POSIX::strftime( '%m%d%H%M%Y.%S', gmtime );
    sys_log("Send NUL request\n");
    send_request( $PROTOCOL_VERSION, $REQUEST_TYPES{NUL},
        { content => $timestamp } );
    sys_log("NUL request sent\n");
    sleep 1;
    usleep($MAINLOOP_SLEEP_MICROSECONDS);
}
