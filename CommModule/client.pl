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
use MIME::Base64;
use POSIX;
use Readonly;
use Time::HiRes qw(usleep);

my $paranoid = 1;

my $debug = 0;

my $log_stdout = 1;

my $gpg_binary     = '/usr/bin/gpg';
my $openssl_binary = '/usr/bin/openssl';

my $serialport          = $ENV{'SERIAL_PORT'}         || '/dev/ttyUSB0';
my $csr_dir             = $ENV{'CSR_DIRECTORY'}       || '../csr';
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

Readonly my $PROTOCOL_VERSION    => 1;
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
Readonly my $MAGIC_BYTES => 'rie4Ech7';

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

my $dbh =
    DBI->connect( "DBI:mysql:$db_name:$db_host", $db_user, $db_password,
    { RaiseError => 1, AutoCommit => 1 } )
    || log_error_and_die('Error establishing the database connection.');

foreach ( keys %revoke_file ) {
    if ( !-f $revoke_file{$_} ) {
        next;
    }
    my $revoke_hash = sha1_hex( read_file( $revoke_file{$_} ) );
    sys_log("Root $_: Hash $revoke_file{$_} = $revoke_hash\n");
}

sub mysql_query {
    my ($query) = @_;
    $dbh->do($query);
    return;
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

Readonly my $ZERO_LENGTH_FIELD => "\N{NULL}\N{NULL}\N{NULL}";
Readonly my $MAX_BLOCK_SIZE    => 2**24;
Readonly my $LENGTH_FIELD_SIZE => 3;

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

Readonly my $DEFAULT_MTU => 30;

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

Readonly my $START_BYTE => chr 0x02;
Readonly my $ACK_BYTE   => chr 0x10;
Readonly my $RESET_BYTE => chr 0x11;

Readonly my $WAIT_FOR_HANDSHAKE_SECONDS => 20;
Readonly my $WAIT_FOR_ACK_SECONDS       => 5;

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

Readonly my $WAIT_FOR_INITIAL_DATA_SECONDS => 120;
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

Readonly my $TRAILING_BYTES_SIZE => $CRC_LENGTH + $MAGIC_BYTES_LENGTH;

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

Readonly my $MINIMUM_POINTS_FOR_ASSURED_MEMBER => 50;
Readonly my $VALIDITY_DAYS_SERVER_ASSURED      => 730;
Readonly my $VALIDITY_DAYS_SERVER_WOT          => 180;

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

    my $stdout = IO::Handle->new();
    my $pid = open3( undef, $stdout, $stdout, $openssl_binary, 'x509', '-in',
        $certificate_filename, '-noout', '-serial' );
    my $data = q{};
    {
        local $INPUT_RECORD_SEPARATOR = undef;
        $data = <$stdout>;
    }
    waitpid $pid, 0;
    if ( $data =~ m/serial=([[:xdigit:]]+)/xms ) {
        return $1;
    }
    return q{};
}

sub OpenPGPextractExpiryDate($) {
    my $r = q{};
    my $cts;
    my @date;

    open( RGPG, $gpg_binary . ' -vv ' . $_[0] . ' 2>&1 |' )
        || log_error_and_die(
        sprintf( "Can't start GnuPG(%s): %s", $gpg_binary, $! ) );
    open( OUT, '> infogpg.txt' )
        || log_error_and_die(
        sprintf( "Can't open output file: infogpg.txt: %s", $! ) );
    $/ = "\n";
    while (<RGPG>) {
        print OUT $_;
        unless ($r) {
            if (/^\s*version \d+, created (\d+), md5len 0, sigclass (?:0x[0-9a-fA-F]+|\d+)\s*$/
                )
            {
                sys_log("Detected CTS: $1\n");
                $cts = int($1);
            }
            elsif (
                /^\s*critical hashed subpkt \d+ len \d+ \(sig expires after ((\d+)y)?((\d+)d)?((\d+)h)?(\d+)m\)\s*$/
                )
            {
                sys_log("Detected FRAME $2 $4 $6 $8\n");
                $cts += $2 * 31536000;    # secs per year (60 * 60 * 24 * 365)
                $cts += $4 * 86400;       # secs per day  (60 * 60 * 24)
                $cts += $6 * 3600;        # secs per hour (60 * 60)
                $cts += $8 * 60;          # secs per min  (60)
                $r = $cts;
            }
            elsif (/version/) {
                sys_log("Detected VERSION\n");
            }
        }
    }

    close(OUT);
    close(RGPG);

    sys_log("CTS: $cts  R: $r\n");

    if ($r) {
        @date = gmtime($r);
        $r    = sprintf(
            '%.4i-%.2i-%.2i %.2i:%.2i:%.2i',    # date format
            $date[5] + 1900, $date[4] + 1, $date[3],    # day
            $date[2], $date[1], $date[0],               # time
        );

    }
    sys_log("$r\n");
    return $r;
}

#sub OpenPGPextractExpiryDate($)
#{
#  my $data=`$gpgbin -v $_[0]`;
#  open OUT,">infogpg.txt";
#  print OUT $data;
#  close OUT;
#  if($data=~m/^sig\s+[0-9A-F]{8} (\d{4}-\d\d-\d\d)   [^\[]/)
#  {
#    return "$1 00:00:00";
#  }
#  return q{};
#}

# Sets the locale according to the users preferred language
sub setUsersLanguage($) {
    my $userid = int( $_[0] );
    my $lang   = "en_US";

    sys_log("Searching for the language of the user $userid\n");
    my @a = $dbh->selectrow_array(
        sprintf( "SELECT language FROM users WHERE id='%d'", $userid ) );
    $lang = $1 if ( $a[0] =~ m/(\w+_[\w.@]+)/ );

    sys_log("The user's preferred language: $lang\n");

    if ( $lang ne q{} ) {
        $ENV{"LANG"} = $lang;
        setlocale( LC_ALL, $lang );
    }
    else {
        $ENV{"LANG"} = "en_US";
        setlocale( LC_ALL, "en_US" );
    }
}

sub getUserData($) {
    return () unless ( $_[0] =~ m/^\d+$/ );
    my $sth = $dbh->prepare("SELECT * FROM users WHERE id='$_[0]'");
    $sth->execute();
    while ( my $rowdata = $sth->fetchrow_hashref() ) {
        return %{$rowdata};
    }
    return ();
}

sub _($) {
    return gettext( $_[0] );
}

sub sendmail($$$$$$$) {
    my ( $to, $subject, $message, $from, $replyto, $toname, $fromname ) = @_;
    my $extra = q{};

# sendmail($user{email}, "[CAcert.org] Your GPG/PGP Key", $body, "support\@cacert.org", q{}, q{}, "CAcert Support");
    my @lines = split( "\n", $message );
    $message = q{};
    foreach my $line (@lines) {
        $line = trim($line);
        if ( $line eq "." ) {
            $message .= " .\n";
        }
        else {
            $message .= $line . "\n";
        }
    }

    $fromname = $from if ( $fromname eq q{} );

    my @bits = split( ",", $from );
    $from     = add_slashes( $bits['0'] );
    $fromname = add_slashes($fromname);

    my $smtp =
        IO::Socket::INET->new( PeerAddr => $smtp_host . ':' . $smtp_port );
    $/ = "\n";
    sys_log( "SMTP: " . <$smtp> );
    print $smtp "EHLO $smtp_helo_name\r\n";
    sys_log( "SMTP: " . <$smtp> );
    print $smtp "MAIL FROM:<$smtp_return_address>\r\n";
    sys_log( "MAIL FROM: " . <$smtp> );

    @bits = split( ",", $to );
    foreach my $user (@bits) {
        print $smtp "RCPT TO:<" . trim($user) . ">\r\n";
        sys_log( "RCPT TO: " . <$smtp> );
    }
    print $smtp "DATA\r\n";
    sys_log( "DATA: " . <$smtp> );

    print $smtp "X-Mailer: $smtp_x_mailer\r\n";
    print $smtp "X-OriginatingIP: " . $ENV{"REMOTE_ADDR"} . "\r\n";
    print $smtp "Sender: $smtp_errors_to\r\n";
    print $smtp "Errors-To: $smtp_errors_to\r\n";
    if ( $replyto ne q{} ) {
        print $smtp "Reply-To: $replyto\r\n";
    }
    else {
        print $smtp "Reply-To: $from\r\n";
    }
    print $smtp "From: $from ($fromname)\r\n";
    print $smtp "To: $to\r\n";
    my $new_subject = encode_base64( trim($subject) );
    $new_subject =~ s/\n*$//;
    print $smtp trim($subject) =~ m/[^a-zA-Z0-9 ,.\[\]\/-]/
        ? "Subject: =?utf-8?B?$new_subject?=\r\n"
        : "Subject: $subject\r\n";
    print $smtp "MIME-Version: 1.0\r\n";
    if ( $extra eq q{} ) {
        print $smtp "Content-Type: text/plain; charset=\"utf-8\"\r\n";
        print $smtp "Content-Transfer-Encoding: 8bit\r\n";
    }
    else {
        print $smtp "Content-Type: text/plain; charset=\"iso-8859-1\"\r\n";
        print $smtp "Content-Transfer-Encoding: quoted-printable\r\n";
        print $smtp "Content-Disposition: inline\r\n";
    }

    #	print $smtp "Content-Transfer-Encoding: BASE64\r\n";
    print $smtp "\r\n";
    print $smtp $message . "\r\n.\r\n";
    sys_log( "ENDOFTEXT: " . <$smtp> );
    print $smtp "QUIT\r\n";
    sys_log( "QUIT: " . <$smtp> );
    close($smtp);
}

sub HandleCerts($$) {
    my $org    = $_[0] ? "org" : q{};
    my $server = $_[1];

    my $table = $org . ( $server ? "domaincerts" : "emailcerts" );

    sys_log("HandleCerts $table\n");

    my $query =
        "SELECT * FROM $table WHERE crt_name='' AND csr_name!='' AND warning<3";
    sys_log("$query\n") if ( $debug >= 1 );
    my $sth = $dbh->prepare($query);
    $sth->execute();
    while ( my $row_data = $sth->fetchrow_hashref() ) {
        my %row      = %{$row_data};
        my $prefix   = $org . ( $server ? "server" : "client" );
        my $short    = int( $row{'id'} / 1000 );
        my $csr_name = sprintf( "%s/%s/%s/%s-%d.csr",
            $csr_dir, $prefix, $short, $prefix, $row{'id'} );
        my $crt_name = sprintf( "%s/%s/%s/%s-%d.crt",
            $crt_dir, $prefix, $short, $prefix, $row{'id'} );

        my $dirname = $crt_name;
        $dirname =~ s/\/[^\/]*\.crt//;
        mkdir $dirname, 0777;
        sys_log("New Layout: $crt_name\n");

        if ( $server == 1 ) {

            #Weird SQL structure ...
            my @sqlres = $dbh->selectrow_array(
                sprintf( "SELECT memid FROM domains WHERE id='%d'",
                    int( $row{'domid'} ) )
            );
            $row{'memid'} = $sqlres[0];
            sys_log("Fetched memid: $row{'memid'}\n") if ( $debug >= 1 );
        }

        sys_log("Opening $csr_name\n");

        my $crt = q{};

        my $profile = 0;

        #   "0"=>"client.cnf",
        #   "1"=>"client-org.cnf",
        #   "2"=>"client-codesign.cnf",
        #   "3"=>"client-machine.cnf",
        #   "4"=>"client-ads.cnf",
        #   "5"=>"server.cnf",
        #   "6"=>"server-org.cnf",
        #   "7"=>"server-jabber.cnf",
        #   "8"=>"server-ocsp.cnf",
        #   "9"=>"server-timestamp.cnf",
        #   "10"=>"proxy.cnf",
        #   "11"=>"subca.cnf"

        if ( $row{"type"} =~ m/^(8|9)$/ ) {
            $profile = $row{"type"};
        }
        elsif ( $org == 1 ) {
            if ( $row{'codesign'} ) {
                $profile = 2;    ## TODO!
            }
            elsif ( $server == 1 ) {
                $profile = 6;
            }
            else {
                $profile = 1;
            }
        }
        else {
            if ( $row{'codesign'} ) {
                $profile = 2;
            }
            elsif ( $server == 1 ) {
                $profile = 5;
            }
            else {
                $profile = 0;
            }
        }

        if ( open( IN, "<$csr_name" ) ) {
            undef $/;
            my $content = <IN>;
            close IN;
            if ( $debug >= 1 ) {
                sys_log("Read $csr_name.\n");
                sys_log("Subject: --$row{'subject'}--\n");
            }

            my ( $SAN, $subject ) =
                x509_extract_subject_altnames( $row{'subject'} );
            if ( $debug >= 1 ) {
                sys_log("Subject: --$subject--\n");
                sys_log("SAN: --$SAN--\n");
                sys_log("memid: $row{'memid'}\n");
            }

            my $days =
                $org
                ? ( $server ? ( 365 * 2 ) : 365 )
                : calculate_validity_days( $row{"memid"} );

            my $md_id =
                exists $MD_ALGORITHMS{ $row{'md'} }
                ? $MD_ALGORITHMS{ $row{'md'} }
                : 0;

            $crt = send_request(
                $PROTOCOL_VERSION,
                $REQUEST_TYPES{SIGN},
                {   id_system    => $IDENTITY_SYSTEMS{X509},
                    root         => $row{'rootcert'} - 1,
                    profile      => $profile,
                    md_algorithm => $md_id,
                    days         => $days,
                    spkac        => $row{'keytype'} eq 'NS' ? 1 : 0,
                    content      => $content,
                    san          => $SAN,
                    $subject     => $subject,
                }
            );
            if ( length($crt) ) {
                if ( $crt =~ m/^-----BEGIN CERTIFICATE-----/ ) {
                    open OUT, ">$crt_name";
                    print OUT $crt;
                    close OUT;
                }
                else {
                    open OUT, ">$crt_name.der";
                    print OUT $crt;
                    close OUT;
                    system
                        "$openssl_binary x509 -in $crt_name.der -inform der -out $crt_name";
                }
            }
            else {
                sys_log("ZERO Length certificate received.\n");
            }
        }
        else {
            sys_log("Error: $! Konnte $csr_name nicht laden\n");
        }

        if ( -s $crt_name ) {
            sys_log("Opening $crt_name\n");

            my $date   = x509_extract_expiry_date($crt_name);
            my $serial = x509_extract_serial_number($crt_name);

            setUsersLanguage( $row{memid} );

            my %user = getUserData( $row{memid} );

            foreach ( sort keys %user ) {
                sys_log("  $_ -> $user{$_}\n") if ( $debug >= 1 );
            }

            my $query = sprintf(
                "UPDATE $table SET crt_name='%s', modified=NOW(), serial='%s', expire='%s' WHERE id='%d'",
                $crt_name, $serial, $date, $row{'id'} );

            sys_log("$query\n");

            $dbh->do($query);

            my $body = _("Hi") . " $user{fname},\n\n";
            $body .= sprintf(
                _(  "You can collect your certificate for %s by going to the following location:"
                    )
                    . "\n\n",
                $row{'email'} . $row{'CN'}
            );
            $body
                .= "https://www.cacert.org/account.php?id="
                . ( $server ? "15" : "6" )
                . "&cert=$row{id}\n\n";
            $body
                .= _(
                "If you have not imported CAcert's root certificate, please go to:"
                ) . "\n";
            $body .= "https://www.cacert.org/index.php?id=3\n";
            $body
                .= "Root cert fingerprint = A6:1B:37:5E:39:0D:9C:36:54:EE:BD:20:31:46:1F:6B\n";
            $body
                .= "Root cert fingerprint = 135C EC36 F49C B8E9 3B1A B270 CD80 8846 76CE 8F33\n\n";
            $body .= _("Best regards") . "\n"
                . _("CAcert.org Support!") . "\n\n";
            sys_log($body);
            sendmail( $user{email}, "[CAcert.org] " . _("Your certificate"),
                $body, "support\@cacert.org", q{}, q{}, "CAcert Support" );
        }
        else {
            sys_log(  "Could not find the issued certificate. $crt_name "
                    . $row{"id"}
                    . "\n" );
            $dbh->do(
                sprintf( "UPDATE $table SET warning=warning+1 WHERE id='%d'",
                    $row{'id'} )
            );
        }
    }
}

sub DoCRL($$) {
    my $crl      = $_[0];
    my $crl_name = $_[1];

    my $crl_directory = dirname($crl_name);
    if ( !-d $crl_directory ) {
        mkdir($crl_directory);
    }

    my $command;
    my $output;

    if ( length($crl) ) {
        if ( $crl =~ m/^-----BEGIN X509 CRL-----/ ) {
            open OUT, ">$crl_name.pem";
            print OUT $crl;
            close OUT;

            $command =
                "$openssl_binary crl -in $crl_name.pem -outform der -out $crl_name.tmp 2>&1";
            $output = qx/$command/;
            sys_log("command $command output:\n$output")
                if ( $? != 0 || $debug >= 1 );
        }
        else {
            open OUT, ">$crl_name.patch";
            print OUT $crl;
            close OUT;

            $command =
                "xdelta patch $crl_name.patch $crl_name $crl_name.tmp 2>&1";
            $output = qx/$command/;
            sys_log("command $command output:\n$output")
                if ( $? != 0 || $debug >= 1 );
            if ( $? != 0 ) {

                # put delta into temporary file for debugging
                open OUT, ">$crl_name.tmp";
                print OUT $crl;
                close OUT;
            }
        }

        $command =
            "openssl crl -verify -in $crl_name.tmp -inform der -noout 2>&1";
        $output = qx/$command/;
        sys_log("command $command output:\n$output")
            if ( $? != 0 || $debug >= 1 );
        if ( $? == 0 ) {
            rename "$crl_name.tmp", "$crl_name";
        }
        else {
            sys_log(
                "VERIFICATION OF NEW CRL DID NOT SUCCEED! PLEASE REPAIR!\n");
            sys_log("Broken CRL is available as $crl_name.tmp\n");
        }
        return 1;
    }
    else {
        sys_log("RECEIVED AN EMPTY CRL!\n");
    }
    return 0;
}

sub RefreshCRLs() {
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
            DoCRL( $crl, $crl_name );
        }
    }
}

sub RevokeCerts($$) {
    my $org    = $_[0] ? "org" : q{};
    my $server = $_[1];

    my $table = $org . ( $server ? "domaincerts" : "emailcerts" );

    my $sth =
        $dbh->prepare(
        "SELECT * FROM $table WHERE revoked='1970-01-01 10:00:01'")
        ;    # WHICH TIMEZONE?
    $sth->execute();
    while ( my $rowdata = $sth->fetchrow_hashref() ) {
        my %row = %{$rowdata};

        my $prefix = $org . ( $server ? "server" : "client" );
        my $short  = int( $row{'id'} / 1000 );

        my $crt_name = sprintf( "%s/%s/%s/%s-%d.crt",
            $crt_dir, $prefix, $short, $prefix, $row{'id'} );
        my $crl_name = $revoke_file{ $row{'rootcert'} };

        if ( open( IN, "<$crt_name" ) ) {
            undef $/;
            my $content = <IN>;
            close IN;
            my $revokehash = sha1_hex( read_file($crl_name) );

            my $crl = send_request(
                $PROTOCOL_VERSION,
                $REQUEST_TYPES{REVOKE},
                {   id_system => $IDENTITY_SYSTEMS{X509},
                    root      => $row{'rootcert'} - 1,
                    days      => 365,
                    content   => $content,
                    subject   => $revokehash,
                }
            );
            my $result = DoCRL( $crl, $crl_name );

            if ($result) {
                $dbh->do( "UPDATE $table SET revoked=NOW() WHERE id='"
                        . $row{'id'}
                        . "'" );

                if ( $org eq q{} ) {
                    if ( $server == 1 ) {
                        my @a = $dbh->selectrow_array(
                                  "SELECT memid FROM domains WHERE id='"
                                . int( $row{domid} )
                                . "'" );
                        sendRevokeMail( $a[0], $row{'CN'}, $row{'serial'} );
                    }
                    else {
                        sendRevokeMail( $row{memid}, $row{'CN'},
                            $row{'serial'} );
                    }
                }
                else {
                    my $orgsth = $dbh->prepare(
                              "SELECT memid FROM org WHERE orgid='"
                            . int( $row{orgid} )
                            . "'" );
                    $orgsth->execute();
                    while ( my ($memid) = $orgsth->fetchrow_array() ) {
                        sendRevokeMail( $memid, $row{'CN'}, $row{'serial'} );
                    }
                }
            }
        }
        else {
            sys_log("Error in RevokeCerts: $crt_name $!\n")
                if ( $debug >= 1 );
        }
    }
}

sub sendRevokeMail() {
    my $memid    = $_[0];
    my $certName = $_[1];
    my $serial   = $_[2];
    setUsersLanguage($memid);

    my %user = getUserData($memid);

    my $body = _("Hi") . " $user{fname},\n\n";
    $body .= sprintf(
        _(  "Your certificate for '%s' with the serial number '%s' has been revoked, as per request."
            )
            . "\n\n",
        $certName,
        $serial
    );
    $body .= _("Best regards") . "\n" . _("CAcert.org Support!") . "\n\n";
    sys_log( "Sending email to " . $user{"email"} . "\n" ) if ( $debug >= 1 );
    sendmail( $user{email}, "[CAcert.org] " . _("Your certificate"),
        $body, "support\@cacert.org", q{}, q{}, "CAcert Support" );
}

sub HandleGPG() {
    my $sth = $dbh->prepare("SELECT * FROM gpg WHERE crt='' AND csr!='' ");
    $sth->execute();
    while ( my $row_data = $sth->fetchrow_hashref() ) {
        my %row = %{$row_data};

        my $prefix   = "gpg";
        my $short    = int( $row{'id'} / 1000 );
        my $csr_name = sprintf( "%s/%s/%s/%s-%d.csr",
            $csr_dir, $prefix, $short, $prefix, $row{'id'} );
        my $crt_name = sprintf( "%s/%s/%s/%s-%d.crt",
            $crt_dir, $prefix, $short, $prefix, $row{'id'} );

        sys_log("Opening $csr_name\n");

        my $crt = q{};

        if ( -s $csr_name && open( IN, "<$csr_name" ) ) {
            undef $/;
            my $content = <IN>;
            close IN;
            sys_log("Read $csr_name.\n");
            $crt = send_request(
                $PROTOCOL_VERSION,
                $REQUEST_TYPES{SIGN},
                {   system_id => $IDENTITY_SYSTEMS{OPENPGP},
                    root =>
                        0, # hard coded for now, signer could support multiple
                    days    => 366,
                    content => $content,
                }
            );
            if ( length $crt ) {
                open OUT, ">$crt_name";
                print OUT $crt;
                close OUT;
            }

        }
        else {
            next;
        }

        if ( -s $crt_name ) {
            sys_log("Opening $crt_name\n");
            setUsersLanguage( $row{memid} );

            my $date = OpenPGPextractExpiryDate($crt_name);
            my %user = getUserData( $row{memid} );

            my $query = sprintf(
                "UPDATE gpg SET crt='%s', issued=NOW(), expire='%s' WHERE id='%d'",
                $crt_name, $date, $row{'id'} );
            sys_log($query) if ( $debug >= 1 );
            $dbh->do($query);

            my $body = _("Hi") . " $user{fname},\n\n";
            $body .= sprintf(
                _("Your CAcert signed key for %s is available online at:")
                    . "\n\n",
                $row{'email'}
            );
            $body .= "https://www.cacert.org/gpg.php?id=3&cert=$row{id}\n\n";
            $body
                .= _(
                "To help improve the trust of CAcert in general, it's appreciated if you could also sign our key and upload it to a key server. Below is a copy of our primary key details:"
                ) . "\n\n";
            $body
                .= "pub 1024D/65D0FD58 2003-07-11 CA Cert Signing Authority (Root CA) <gpg\@cacert.org>\n";
            $body
                .= "Key fingerprint = A31D 4F81 EF4E BD07 B456 FA04 D2BB 0D01 65D0 FD58\n\n";
            $body .= _("Best regards") . "\n"
                . _("CAcert.org Support!") . "\n\n";
            sendmail( $user{email}, "[CAcert.org] Your GPG/PGP Key",
                $body, "support\@cacert.org", q{}, q{}, "CAcert Support" );
        }
        else {
            sys_log(
                "Could not find the issued gpg key. " . $row{"id"} . "\n" );
        }
    }
}

# Main program loop

my $crlcheck = 0;

$SIG{INT}  = \&signal_handler;
$SIG{TERM} = \&signal_handler;

sub signal_handler {
    log_error_and_die("Caught signal $!");
}

while ( -f "./client.pl-active" ) {
    sys_log("Handling GPG database ...\n");
    HandleGPG();
    sys_log("Issueing certs ...\n");
    HandleCerts( 0, 0 );    #personal client certs
    HandleCerts( 0, 1 );    #personal server certs
    HandleCerts( 1, 0 );    #org client certs
    HandleCerts( 1, 1 );    #org server certs
    sys_log("Revoking certs ...\n");
    RevokeCerts( 0, 0 );    #personal client certs
    RevokeCerts( 0, 1 );    #personal server certs
    RevokeCerts( 1, 0 );    #org client certs
    RevokeCerts( 1, 1 );    #org server certs

    $crlcheck++;
    RefreshCRLs() if ( ( $crlcheck % 100 ) == 1 );

    my $timestamp = POSIX::strftime( '%m%d%H%M%Y.%S', gmtime );
    sys_log("Send NUL request\n");
    send_request( $PROTOCOL_VERSION, $REQUEST_TYPES{NUL},
        { content => $timestamp } );
    sys_log("NUL request sent\n");
    sleep 1;
    usleep(1_700_000);
}
