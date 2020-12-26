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
use Device::SerialPort qw(:PARAM :STAT 0.07);
use POSIX;
use IO::Select;
use Time::HiRes qw(usleep);
use File::CounterFile;
use File::Basename qw(dirname);
use IPC::Open3;
use File::Copy;
use DBI;
use Locale::gettext;
use IO::Socket;
use MIME::Base64;
use Digest::SHA qw(sha1_hex);

#Protocol version:
my $ver = 1;

my $paranoid = 1;

my $debug = 0;

my $log_stdout = 1;

my $serialport = $ENV{"SERIAL_PORT"};
my $csr_dir;
if ($ENV{'CSR_DIRECTORY'}) {
  $csr_dir = $ENV{'CSR_DIRECTORY'};
}
else {
  $csr_dir = '../csr';
}
my $crt_dir;
if ($ENV{'CRT_DIRECTORY'}) {
  $crt_dir = $ENV{'CRT_DIRECTORY'};
}
else {
  $crt_dir = '../crt';
}
my $crl_dir;
if ($ENV{'CRL_DIRECTORY'}) {
  $crl_dir = $ENV{'CRL_DIRECTORY'};
}
else {
  $crl_dir = '../www';
}

my $gpg_binary     = "/usr/bin/gpg";
my $openssl_binary = "/usr/bin/openssl";

my %revoke_file =
  (2 => "$crl_dir/class3-revoke.crl", 1 => "$crl_dir/revoke.crl");

my $smtp_host;
if ($ENV{'SMTP_HOST'}) {
  $smtp_host = $ENV{'SMTP_HOST'};
}
else {
  $smtp_host = 'localhost';
}
my $smtp_port;
if ($ENV{'SMTP_PORT'}) {
  $smtp_port = $ENV{'SMTP_PORT'};
}
else {
  $smtp_port = '25';
}
my $smtp_helo_name      = "hlin.cacert.org";
my $smtp_return_address = "returns\@cacert.org";
my $smtp_x_mailer       = "CAcert.org Website";
my $smtp_errors_to      = "returns\@cacert.org";

#End of configurations

########################################################

my %monarr = (
  "Jan" => 1,
  "Feb" => 2,
  "Mar" => 3,
  "Apr" => 4,
  "May" => 5,
  "Jun" => 6,
  "Jul" => 7,
  "Aug" => 8,
  "Sep" => 9,
  "Oct" => 10,
  "Nov" => 11,
  "Dec" => 12
);

my $dbh = DBI->connect(
  "DBI:mysql:$ENV{'MYSQL_WEBDB_DATABASE'}:$ENV{'MYSQL_WEBDB_HOSTNAME'}",
  $ENV{'MYSQL_WEBDB_USER'},
  $ENV{'MYSQL_WEBDB_PASSWORD'},
  { RaiseError => 1, AutoCommit => 1 }
) || die("Error with the database connection.\n");

sub readfile($) {
  my $save = $/;
  undef $/;
  open READIN, "<$_[0]";
  my $content = <READIN>;
  close READIN;
  $/ = $save;
  return $content;
}

#Logging functions:
my $lastdate = "";

sub SysLog($) {
  return if (not defined($_[0]));
  my $timestamp = POSIX::strftime("%Y-%m-%d %H:%M:%S", localtime);
  my $currdate  = substr($timestamp, 0, 10);
  if ($lastdate ne $currdate) {
    close LOG if ($lastdate ne "");
    $lastdate = $currdate;
    open LOG, ">>logfile$lastdate.txt";
  }
  print LOG "$timestamp $_[0]";
  flush LOG;
  print "$timestamp $_[0]" if ($log_stdout == 1);
  select()->flush();
}

sub LogErrorAndDie($) {
  SysLog($_[0]);
  if ($paranoid == 1) {
    die $_[0];
  }
}

foreach (keys %revoke_file) {
  next unless (-f $revoke_file{$_});
  my $revoke_hash = sha1_hex(readfile($revoke_file{$_}));
  SysLog("Root $_: Hash $revoke_file{$_} = $revoke_hash\n");
}

sub mysql_query($) {
  $dbh->do($_[0]);
}

sub trim($) {
  my $new = $_[0];
  $new =~ s/^\s*//;
  $new =~ s/\s*$//;
  return ($new);
}

sub addslashes($) {
  my $new = $_[0];
  $new =~ s/['"\\]/\\$1/g;
  return ($new);
}

sub recode {
  return $_[1];
}

SysLog("Opening Serial interface:\n");

sub SerialSettings($) {
  my $PortObj = $_[0];
  if (!defined($PortObj)) {
    LogErrorAndDie("Could not open Serial Port!\n");
  }
  else {
    $PortObj->baudrate(115200);
    $PortObj->parity("none");
    $PortObj->databits(8);
    $PortObj->stopbits(1);
  }
}

#We have to open the SerialPort and close it again, so that we can bind it to a Handle
if (!-f "serial.conf") {
  my $PortObj = new Device::SerialPort($serialport);
  SerialSettings($PortObj);
  $PortObj->save("serial.conf");
  undef $PortObj;
}

my Device::SerialPort $PortObj = tie(*SER, 'Device::SerialPort', "serial.conf")
  || LogErrorAndDie("Can't tie using Configuration_File_Name: $!\n");

LogErrorAndDie("Could not open Serial Interface!\n") if (not defined($PortObj));
SerialSettings($PortObj);

#open SER,">$serialport";

SysLog("Serial interface opened: $PortObj\n");

my $sel = IO::Select->new(\*SER);

#Hexdump function: Returns the hexdump representation of a string
sub hexdump($) {
  return "" if (not defined($_[0]));
  my $content = "";
  $content .= sprintf("%02X ", unpack("C", substr($_[0], $_, 1)))
    foreach (0 .. length($_[0]) - 1);
  return $content;
}

#pack3 packs together the length of the data in 3 bytes and the data itself, size limited to 16MB. In case the data is more than 16 MB, it is ignored, and a 0 Byte block is transferred
sub pack3 {
  return "\x00\x00\x00" if (!defined($_[0]));
  my $data = (length($_[0]) >= 2**24) ? "" : $_[0];
  my $len  = pack("N", length($data));
  SysLog("len: " . length($data) . "\n") if ($debug >= 1);
  return substr($len, 1, 3) . $data;
}

#unpack3 unpacks packed data.
sub unpack3($) {
  return undef if ((not defined($_[0])) or length($_[0]) < 3);
  SysLog("hexdump: " . hexdump("\x00" . substr($_[0], 0, 3)) . "\n")
    if ($debug >= 1);
  my $len = unpack("N", "\x00" . substr($_[0], 0, 3));
  SysLog("len3: $len length(): "
      . length($_[0])
      . " length()-3: "
      . (length($_[0]) - 3) . "\n")
    if ($debug >= 1);
  return undef if (length($_[0]) - 3 != $len);
  return substr($_[0], 3);
}

# unpack3array extracts a whole array of concatented pack3ed data.
sub unpack3array($) {
  my @retarr = ();
  if ((not defined($_[0])) or length($_[0]) < 3) {
    SysLog("Begin of structure corrupt\n");
    return ();
  }
  my $dataleft = $_[0];
  while (length($dataleft) >= 3) {
    SysLog("hexdump: " . hexdump("\x00" . substr($dataleft, 0, 3)) . "\n")
      if ($debug >= 1);
    my $len = unpack("N", "\x00" . substr($dataleft, 0, 3));
    SysLog("len3: $len length(): "
        . length($dataleft)
        . " length()-3: "
        . (length($dataleft) - 3) . "\n")
      if ($debug >= 1);
    if (length($dataleft) - 3 < $len) {
      SysLog("Structure cut off\n");
      return ();
    }
    push @retarr, substr($dataleft, 3, $len);
    $dataleft = substr($dataleft, 3 + $len);
  }
  if (length($dataleft) != 0) {
    SysLog("End of structure cut off\n");
    return ();
  }
  return @retarr;
}

# Raw send function over the Serial Interface  (+debugging)
sub SendIt($) {
  return unless defined($_[0]);
  SysLog(sprintf("Sending %d bytes\n", length($_[0]))) if ($debug >= 1);
  my $data  = $_[0];
  my $total = 0;
  my $mtu   = 30;
  while (length($data)) {
    my $iwrote = scalar($PortObj->write(substr($data, 0, $mtu))) || 0;
    $total += $iwrote;
    $data = substr($data, $iwrote);
    SysLog(sprintf(
      "Wrote: %d bytes total: %d bytes left: %d bytes\n",
      $iwrote, $total, length($data)
    ))
      if ($debug >= 1);
  }
  SysLog("Sent message.\n") if ($debug >= 1);
}

#Send data over the Serial Interface with handshaking:
sub SendHandshaked($) {
  SysLog("Shaking hands ...\n") if ($debug >= 1);
  SendIt("\x02");

  LogErrorAndDie("Handshake uncompleted. Connection lost2! $!\n")
    if (!scalar($sel->can_read(20)));
  my $data   = "";
  my $length = read SER, $data, 1;
  if ($length && $data eq "\x10") {

    my $xor = 0;
    foreach (0 .. length($_[0]) - 1) {

      $xor ^= unpack("C", substr($_[0], $_, 1));
    }

    my $try_again = 1;
    while ($try_again == 1) {
      SendIt($_[0] . pack("C", $xor) . "rie4Ech7");

      LogErrorAndDie(
        "Packet receipt was not confirmed in 5 seconds. Connection lost!\n")
        if (!scalar($sel->can_read(5)));

      $data   = "";
      $length = read SER, $data, 1;

      if ($length && $data eq "\x10") {
        SysLog("Sent successfully!...\n") if ($debug >= 1);
        $try_again = 0;
      }
      elsif ($length && $data eq "\x11") {
        $try_again = 1;
      }
      else {
        LogErrorAndDie(sprintf(
          "I cannot send! %d %s\n", $length, unpack("C", $data)));
      }
    }

  }
  else {
    LogErrorAndDie("!Cannot send! $length\n");
  }
}

sub Receive {
  my $data  = "";
  my @ready = $sel->can_read(120);

  my $length = read SER, $data, 1, 0;

  SysLog("Data: " . hexdump($data) . "\n") if ($debug >= 1);

  if ($data eq "\x02") {
    SysLog("Start received, sending OK\n") if ($debug >= 1);
    SendIt("\x10");

    my $block          = "";
    my $block_finished = 0;
    my $tries          = 100000;

    while ($block_finished == 0) {
      LogErrorAndDie("Tried reading too often\n") if (($tries--) <= 0);
      SysLog("tries: $tries") if (!($tries % 10) && ($debug >= 1));

      $data = "";
      if (!scalar($sel->can_read(5))) {
        LogErrorAndDie("Handshake uncompleted. Connection lost variant3! $!\n");
        return;
      }
      $length = read SER, $data, 100, 0;
      if ($length > 0) {
        $block .= $data;
      }
      $block_finished = defined(unpack3(substr($block, 0, -9))) ? 1 : 0;

      if (!$block_finished and substr($block, -8, 8) eq "rie4Ech7") {
        SysLog("BROKEN Block detected!\n");
        SendIt("\x11");
        $block          = "";
        $block_finished = 0;
        $tries          = 100000;
      }

    }
    SysLog("Block done: " . hexdump($block) . "\n") if ($debug >= 1);
    SendIt("\x10");
    return ($block);
  }
  else {
    LogErrorAndDie("Error: No Answer received, Timeout.\n")
      if (length($data) == 0);
    LogErrorAndDie("Error: Wrong Startbyte: " . hexdump($data) . " !\n");
  }

  SysLog("Waiting on next request ...\n");
}

# @result(Version,Action,Errorcode,Response)=Request(Version=1,Action=1,System=1,Root=1,Configuration="...",Parameter="...",Request="...");
sub Request($$$$$$$$$$$) {
  SysLog(
    "Version: $_[0] Action: $_[1] System: $_[2] Root: $_[3] Config: $_[4]\n")
    if ($debug >= 1);
  $_[3] = 0 if ($_[3] < 0);
  SendHandshaked(pack3(
    pack3(pack("C*",
      $_[0], $_[1],      $_[2],       $_[3], $_[4],
      $_[5], $_[6] >> 8, $_[6] & 255, $_[7]))
      . pack3($_[8])
      . pack3($_[9])
      . pack3($_[10])
  ));
  my $data   = Receive();
  my @fields = unpack3array(substr($data, 3, -9));

  SysLog("Answer from Server: " . hexdump($data) . "\n") if ($debug >= 1);
  return $fields[1];
}

sub calculateDays($) {
  if ($_[0]) {
    my @sum = $dbh->selectrow_array(sprintf(
      "SELECT SUM(points) AS total FROM notary WHERE `to` ='%s' AND deleted = 0 GROUP BY `to`",
      $_[0]));
    SysLog("Summe: $sum[0]\n") if ($debug >= 1);

    return ($sum[0] >= 50) ? 730 : 180;
  }
  return 180;
}

sub X509extractSAN($) {
  my @bits       = split("/", $_[0]);
  my $SAN        = "";
  my $newsubject = "";
  foreach my $val (@bits) {
    my @bit = split("=", $val);
    if ($bit[0] eq "subjectAltName") {
      $SAN .= "," if ($SAN ne "");
      $SAN .= trim($bit[1]);
    }
    else {
      $newsubject .= "/" . $val;
    }
  }
  $newsubject =~ s{^//}{/};
  $newsubject =~ s/[\n\r\t\x00"\\']//g;
  $SAN        =~ s/[ \n\r\t\x00"\\']//g;
  return ($SAN, $newsubject);
}

sub X509extractExpiryDate($) {

  # TIMEZONE ?!?
  my $data = `$openssl_binary x509 -in "$_[0]" -noout -enddate`;

  #notAfter=Aug  8 10:26:34 2007 GMT
  if ($data =~
    m/notAfter=(\w{2,4}) *(\d{1,2}) *(\d{1,2}:\d{1,2}:\d{1,2}) (\d{4}) GMT/)
  {
    my $date = "$4-" . $monarr{$1} . "-$2 $3";
    SysLog("Expiry Date found: $date\n") if ($debug >= 1);
    return $date;
  }
  else {
    SysLog("Expiry Date not found: $data\n");
  }
  return "";
}

sub CRLuptodate($) {
  return 0 unless (-f $_[0]);
  my $data = `$openssl_binary crl -in "$_[0]" -noout -lastupdate -inform der`;
  SysLog("CRL: $data");

  #lastUpdate=Aug  8 10:26:34 2007 GMT
  # Is the timezone handled properly?
  if ($data =~
    m/lastUpdate=(\w{2,4}) *(\d{1,2}) *(\d{1,2}:\d{1,2}:\d{1,2}) (\d{4}) GMT/)
  {
    my $date = sprintf("%04d-%02d-%02d", $4, $monarr{$1}, $2);
    SysLog("CRL Issueing Date found: $date\n") if ($debug >= 1);
    my $compare = strftime("%Y-%m-%d", localtime);
    SysLog("Comparing $date with $compare\n") if ($debug >= 1);
    return $date eq $compare;
  }
  else {
    SysLog(
      "Expiry Date not found. Perhaps DER format is necessary? Hint: $data\n");
  }
  return 0;
}

sub X509extractSerialNumber($) {

  # TIMEZONE ?!?
  my $data = `$openssl_binary x509 -in "$_[0]" -noout -serial`;
  if ($data =~ m/serial=([0-9A-F]+)/) {
    return $1;
  }
  return "";
}

sub OpenPGPextractExpiryDate($) {
  my $r = "";
  my $cts;
  my @date;

  open(RGPG, $gpg_binary . ' -vv ' . $_[0] . ' 2>&1 |')
    or LogErrorAndDie('Can\'t start GnuPG($gpgbin): ' . $! . "\n");
  open(OUT, '> infogpg.txt')
    or LogErrorAndDie('Can\'t open output file: infogpg.txt: ' . $!);
  $/ = "\n";
  while (<RGPG>) {
    print OUT $_;
    unless ($r) {
      if (
        /^\s*version \d+, created (\d+), md5len 0, sigclass (?:0x[0-9a-fA-F]+|\d+)\s*$/
        )
      {
        SysLog("Detected CTS: $1\n");
        $cts = int($1);
      }
      elsif (
        /^\s*critical hashed subpkt \d+ len \d+ \(sig expires after ((\d+)y)?((\d+)d)?((\d+)h)?(\d+)m\)\s*$/
        )
      {
        SysLog("Detected FRAME $2 $4 $6 $8\n");
        $cts += $2 * 31536000;    # secs per year (60 * 60 * 24 * 365)
        $cts += $4 * 86400;       # secs per day  (60 * 60 * 24)
        $cts += $6 * 3600;        # secs per hour (60 * 60)
        $cts += $8 * 60;          # secs per min  (60)
        $r = $cts;
      }
      elsif (/version/) {
        SysLog("Detected VERSION\n");
      }
    }
  }

  close(OUT);
  close(RGPG);

  SysLog("CTS: $cts  R: $r\n");

  if ($r) {
    @date = gmtime($r);
    $r    = sprintf(
      '%.4i-%.2i-%.2i %.2i:%.2i:%.2i',    # date format
      $date[5] + 1900, $date[4] + 1, $date[3],    # day
      $date[2], $date[1], $date[0],               # time
    );

  }
  SysLog("$r\n");
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
#  return "";
#}

# Sets the locale according to the users preferred language
sub setUsersLanguage($) {
  my $userid = int($_[0]);
  my $lang   = "en_US";

  SysLog("Searching for the language of the user $userid\n");
  my @a = $dbh->selectrow_array(
    sprintf("SELECT language FROM users WHERE id='%d'", $userid));
  $lang = $1 if ($a[0] =~ m/(\w+_[\w.@]+)/);

  SysLog("The user's preferred language: $lang\n");

  if ($lang ne "") {
    $ENV{"LANG"} = $lang;
    setlocale(LC_ALL, $lang);
  }
  else {
    $ENV{"LANG"} = "en_US";
    setlocale(LC_ALL, "en_US");
  }
}

sub getUserData($) {
  return () unless ($_[0] =~ m/^\d+$/);
  my $sth = $dbh->prepare("SELECT * FROM users WHERE id='$_[0]'");
  $sth->execute();
  while (my $rowdata = $sth->fetchrow_hashref()) {
    return %{$rowdata};
  }
  return ();
}

sub _($) {
  return gettext($_[0]);
}

sub sendmail($$$$$$$) {
  my ($to, $subject, $message, $from, $replyto, $toname, $fromname) = @_;
  my $extra = "";

  # sendmail($user{email}, "[CAcert.org] Your GPG/PGP Key", $body, "support\@cacert.org", "", "", "CAcert Support");
  my @lines = split("\n", $message);
  $message = "";
  foreach my $line (@lines) {
    $line = trim($line);
    if ($line eq ".") {
      $message .= " .\n";
    }
    else {
      $message .= $line . "\n";
    }
  }

  $fromname = $from if ($fromname eq "");

  my @bits = split(",", $from);
  $from     = addslashes($bits['0']);
  $fromname = addslashes($fromname);

  my $smtp = IO::Socket::INET->new(PeerAddr => $smtp_host . ':' . $smtp_port);
  $/ = "\n";
  SysLog("SMTP: " . <$smtp>);
  print $smtp "EHLO $smtp_helo_name\r\n";
  SysLog("SMTP: " . <$smtp>);
  print $smtp "MAIL FROM:<$smtp_return_address>\r\n";
  SysLog("MAIL FROM: " . <$smtp>);

  @bits = split(",", $to);
  foreach my $user (@bits) {
    print $smtp "RCPT TO:<" . trim($user) . ">\r\n";
    SysLog("RCPT TO: " . <$smtp>);
  }
  print $smtp "DATA\r\n";
  SysLog("DATA: " . <$smtp>);

  print $smtp "X-Mailer: $smtp_x_mailer\r\n";
  print $smtp "X-OriginatingIP: " . $ENV{"REMOTE_ADDR"} . "\r\n";
  print $smtp "Sender: $smtp_errors_to\r\n";
  print $smtp "Errors-To: $smtp_errors_to\r\n";
  if ($replyto ne "") {
    print $smtp "Reply-To: $replyto\r\n";
  }
  else {
    print $smtp "Reply-To: $from\r\n";
  }
  print $smtp "From: $from ($fromname)\r\n";
  print $smtp "To: $to\r\n";
  my $new_subject = encode_base64(recode("html..utf-8", trim($subject)));
  $new_subject =~ s/\n*$//;
  print $smtp trim($subject) =~ m/[^a-zA-Z0-9 ,.\[\]\/-]/
    ? "Subject: =?utf-8?B?$new_subject?=\r\n"
    : "Subject: $subject\r\n";
  print $smtp "MIME-Version: 1.0\r\n";
  if ($extra eq "") {
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
  print $smtp recode("html..utf-8", $message) . "\r\n.\r\n";
  SysLog("ENDOFTEXT: " . <$smtp>);
  print $smtp "QUIT\r\n";
  SysLog("QUIT: " . <$smtp>);
  close($smtp);
}

sub HandleCerts($$) {
  my $org    = $_[0] ? "org" : "";
  my $server = $_[1];

  my $table = $org . ($server ? "domaincerts" : "emailcerts");

  SysLog("HandleCerts $table\n");

  my $query =
    "SELECT * FROM $table WHERE crt_name='' AND csr_name!='' AND warning<3";
  SysLog("$query\n") if ($debug >= 1);
  my $sth = $dbh->prepare($query);
  $sth->execute();
  while (my $row_data = $sth->fetchrow_hashref()) {
    my %row      = %{$row_data};
    my $prefix   = $org . ($server ? "server" : "client");
    my $short    = int($row{'id'} / 1000);
    my $csr_name = sprintf("%s/%s/%s/%s-%d.csr",
      $csr_dir, $prefix, $short, $prefix, $row{'id'});
    my $crt_name = sprintf("%s/%s/%s/%s-%d.crt",
      $crt_dir, $prefix, $short, $prefix, $row{'id'});

    my $dirname = $crt_name;
    $dirname =~ s/\/[^\/]*\.crt//;
    mkdir $dirname, 0777;
    SysLog("New Layout: $crt_name\n");

    if ($server == 1) {

      #Weird SQL structure ...
      my @sqlres = $dbh->selectrow_array(sprintf(
        "SELECT memid FROM domains WHERE id='%d'", int($row{'domid'})));
      $row{'memid'} = $sqlres[0];
      SysLog("Fetched memid: $row{'memid'}\n") if ($debug >= 1);
    }

    SysLog("Opening $csr_name\n");

    my $crt = "";

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

    if ($row{"type"} =~ m/^(8|9)$/) {
      $profile = $row{"type"};
    }
    elsif ($org == 1) {
      if ($row{'codesign'}) {
        $profile = 2;    ## TODO!
      }
      elsif ($server == 1) {
        $profile = 6;
      }
      else {
        $profile = 1;
      }
    }
    else {
      if ($row{'codesign'}) {
        $profile = 2;
      }
      elsif ($server == 1) {
        $profile = 5;
      }
      else {
        $profile = 0;
      }
    }

    if (open(IN, "<$csr_name")) {
      undef $/;
      my $content = <IN>;
      close IN;
      SysLog("Read $csr_name.\n")              if ($debug >= 1);
      SysLog("Subject: --$row{'subject'}--\n") if ($debug >= 1);

      my ($SAN, $subject) = X509extractSAN($row{'subject'});
      SysLog("Subject: --$subject--\n") if ($debug >= 1);
      SysLog("SAN: --$SAN--\n")         if ($debug >= 1);
      SysLog("memid: $row{'memid'}\n")  if ($debug >= 1);

      my $days =
        $org ? ($server ? (365 * 2) : 365) : calculateDays($row{"memid"});

      my $md_id = 0;
      $md_id = 1  if ($row{'md'} eq "md5");
      $md_id = 2  if ($row{'md'} eq "sha1");
      $md_id = 3  if ($row{'md'} eq "rmd160");
      $md_id = 8  if ($row{'md'} eq "sha256");
      $md_id = 9  if ($row{'md'} eq "sha384");
      $md_id = 10 if ($row{'md'} eq "sha512");

      $crt = Request(
        $ver, 1, 1, $row{'rootcert'} - 1,
        $profile, $md_id, $days, $row{'keytype'} eq "NS" ? 1 : 0,
        $content, $SAN, $subject
      );
      if (length($crt)) {
        if ($crt =~ m/^-----BEGIN CERTIFICATE-----/) {
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
        SysLog("ZERO Length certificate received.\n");
      }
    }
    else {
      SysLog("Error: $! Konnte $csr_name nicht laden\n");
    }

    if (-s $crt_name) {
      SysLog("Opening $crt_name\n");

      my $date   = X509extractExpiryDate($crt_name);
      my $serial = X509extractSerialNumber($crt_name);

      setUsersLanguage($row{memid});

      my %user = getUserData($row{memid});

      foreach (sort keys %user) {
        SysLog("  $_ -> $user{$_}\n") if ($debug >= 1);
      }

      my $query = sprintf(
        "UPDATE $table SET crt_name='%s', modified=NOW(), serial='%s', expire='%s' WHERE id='%d'",
        $crt_name, $serial, $date, $row{'id'});

      SysLog("$query\n");

      $dbh->do($query);

      my $body = _("Hi") . " $user{fname},\n\n";
      $body .= sprintf(
        _(
          "You can collect your certificate for %s by going to the following location:"
          )
          . "\n\n",
        $row{'email'} . $row{'CN'}
      );
      $body .=
          "https://www.cacert.org/account.php?id="
        . ($server ? "15" : "6")
        . "&cert=$row{id}\n\n";
      $body .=
        _("If you have not imported CAcert's root certificate, please go to:")
        . "\n";
      $body .= "https://www.cacert.org/index.php?id=3\n";
      $body .=
        "Root cert fingerprint = A6:1B:37:5E:39:0D:9C:36:54:EE:BD:20:31:46:1F:6B\n";
      $body .=
        "Root cert fingerprint = 135C EC36 F49C B8E9 3B1A B270 CD80 8846 76CE 8F33\n\n";
      $body .= _("Best regards") . "\n" . _("CAcert.org Support!") . "\n\n";
      SysLog($body);
      sendmail($user{email}, "[CAcert.org] " . _("Your certificate"),
        $body, "support\@cacert.org", "", "", "CAcert Support");
    }
    else {
      SysLog("Could not find the issued certificate. $crt_name "
          . $row{"id"}
          . "\n");
      $dbh->do(sprintf("UPDATE $table SET warning=warning+1 WHERE id='%d'",
        $row{'id'}));
    }
  }
}

sub DoCRL($$) {
  my $crl      = $_[0];
  my $crl_name = $_[1];

  my $crl_directory = dirname($crl_name);
  if (!-d $crl_directory) {
    mkdir($crl_directory);
  }

  my $command;
  my $output;

  if (length($crl)) {
    if ($crl =~ m/^-----BEGIN X509 CRL-----/) {
      open OUT, ">$crl_name.pem";
      print OUT $crl;
      close OUT;

      $command =
        "$openssl_binary crl -in $crl_name.pem -outform der -out $crl_name.tmp 2>&1";
      $output = qx/$command/;
      SysLog("command $command output:\n$output") if ($? != 0 || $debug >= 1);
    }
    else {
      open OUT, ">$crl_name.patch";
      print OUT $crl;
      close OUT;

      $command = "xdelta patch $crl_name.patch $crl_name $crl_name.tmp 2>&1";
      $output  = qx/$command/;
      SysLog("command $command output:\n$output") if ($? != 0 || $debug >= 1);
      if ($? != 0) {

        # put delta into temporary file for debugging
        open OUT, ">$crl_name.tmp";
        print OUT $crl;
        close OUT;
      }
    }

    $command = "openssl crl -verify -in $crl_name.tmp -inform der -noout 2>&1";
    $output  = qx/$command/;
    SysLog("command $command output:\n$output") if ($? != 0 || $debug >= 1);
    if ($? == 0) {
      rename "$crl_name.tmp", "$crl_name";
    }
    else {
      SysLog("VERIFICATION OF NEW CRL DID NOT SUCCEED! PLEASE REPAIR!\n");
      SysLog("Broken CRL is available as $crl_name.tmp\n");
    }
    return 1;
  }
  else {
    SysLog("RECEIVED AN EMPTY CRL!\n");
  }
  return 0;
}

sub RefreshCRLs() {
  foreach my $rootcert (keys %revoke_file) {
    if (!CRLuptodate($revoke_file{$rootcert})) {
      SysLog("Update of the CRL $rootcert is necessary!\n");
      my $crl_name = $revoke_file{$rootcert};
      my $revoke_hash;
      if (-f $crl_name) {
        $revoke_hash = sha1_hex(readfile($crl_name));
      }
      else {
        $revoke_hash = sha1_hex('');
      }
      my $crl =
        Request($ver, 2, 1, $rootcert - 1, 0, 0, 365, 0, "", "", $revoke_hash);
      SysLog("Received " . length($crl) . " " . hexdump($crl) . "\n")
        if ($debug >= 1);
      DoCRL($crl, $crl_name);
    }
  }
}

sub RevokeCerts($$) {
  my $org    = $_[0] ? "org" : "";
  my $server = $_[1];

  my $table = $org . ($server ? "domaincerts" : "emailcerts");

  my $sth =
    $dbh->prepare("SELECT * FROM $table WHERE revoked='1970-01-01 10:00:01'")
    ;    # WHICH TIMEZONE?
  $sth->execute();
  while (my $rowdata = $sth->fetchrow_hashref()) {
    my %row = %{$rowdata};

    my $prefix = $org . ($server ? "server" : "client");
    my $short  = int($row{'id'} / 1000);

    my $crt_name = sprintf("%s/%s/%s/%s-%d.crt",
      $crt_dir, $prefix, $short, $prefix, $row{'id'});
    my $crl_name = $revoke_file{ $row{'rootcert'} };

    if (open(IN, "<$crt_name")) {
      undef $/;
      my $content = <IN>;
      close IN;
      my $revokehash = sha1_hex(readfile($crl_name));

      my $crl = Request($ver, 2, 1, $row{'rootcert'} - 1,
        0, 0, 365, 0, $content, "", $revokehash);
      my $result = DoCRL($crl, $crl_name);

      if ($result) {
        $dbh->do(
          "UPDATE $table SET revoked=NOW() WHERE id='" . $row{'id'} . "'");

        if ($org eq "") {
          if ($server == 1) {
            my @a = $dbh->selectrow_array(
              "SELECT memid FROM domains WHERE id='" . int($row{domid}) . "'");
            sendRevokeMail($a[0], $row{'CN'}, $row{'serial'});
          }
          else {
            sendRevokeMail($row{memid}, $row{'CN'}, $row{'serial'});
          }
        }
        else {
          my $orgsth = $dbh->prepare(
            "SELECT memid FROM org WHERE orgid='" . int($row{orgid}) . "'");
          $orgsth->execute();
          while (my ($memid) = $orgsth->fetchrow_array()) {
            sendRevokeMail($memid, $row{'CN'}, $row{'serial'});
          }
        }
      }
    }
    else {
      SysLog("Error in RevokeCerts: $crt_name $!\n") if ($debug >= 1);
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
    _(
      "Your certificate for '%s' with the serial number '%s' has been revoked, as per request."
      )
      . "\n\n",
    $certName,
    $serial
  );
  $body .= _("Best regards") . "\n" . _("CAcert.org Support!") . "\n\n";
  SysLog("Sending email to " . $user{"email"} . "\n") if ($debug >= 1);
  sendmail($user{email}, "[CAcert.org] " . _("Your certificate"),
    $body, "support\@cacert.org", "", "", "CAcert Support");
}

sub HandleGPG() {
  my $sth = $dbh->prepare("SELECT * FROM gpg WHERE crt='' AND csr!='' ");
  $sth->execute();
  while (my $row_data = $sth->fetchrow_hashref()) {
    my %row = %{$row_data};

    my $prefix   = "gpg";
    my $short    = int($row{'id'} / 1000);
    my $csr_name = sprintf("%s/%s/%s/%s-%d.csr",
      $csr_dir, $prefix, $short, $prefix, $row{'id'});
    my $crt_name = sprintf("%s/%s/%s/%s-%d.crt",
      $crt_dir, $prefix, $short, $prefix, $row{'id'});

    SysLog("Opening $csr_name\n");

    my $crt = "";

    if (-s $csr_name && open(IN, "<$csr_name")) {
      undef $/;
      my $content = <IN>;
      close IN;
      SysLog("Read $csr_name.\n");
      $crt = Request($ver, 1, 2, 0, 0, 2, 366, 0, $content, "", "");
      if (length($crt)) {
        open OUT, ">$crt_name";
        print OUT $crt;
        close OUT;
      }

    }
    else {
      next;
    }

    if (-s $crt_name) {
      SysLog("Opening $crt_name\n");
      setUsersLanguage($row{memid});

      my $date = OpenPGPextractExpiryDate($crt_name);
      my %user = getUserData($row{memid});

      my $query = sprintf(
        "UPDATE gpg SET crt='%s', issued=NOW(), expire='%s' WHERE id='%d'",
        $crt_name, $date, $row{'id'});
      SysLog($query) if ($debug >= 1);
      $dbh->do($query);

      my $body = _("Hi") . " $user{fname},\n\n";
      $body .= sprintf(
        _("Your CAcert signed key for %s is available online at:") . "\n\n",
        $row{'email'}
      );
      $body .= "https://www.cacert.org/gpg.php?id=3&cert=$row{id}\n\n";
      $body .= _(
        "To help improve the trust of CAcert in general, it's appreciated if you could also sign our key and upload it to a key server. Below is a copy of our primary key details:"
      ) . "\n\n";
      $body .=
        "pub 1024D/65D0FD58 2003-07-11 CA Cert Signing Authority (Root CA) <gpg\@cacert.org>\n";
      $body .=
        "Key fingerprint = A31D 4F81 EF4E BD07 B456 FA04 D2BB 0D01 65D0 FD58\n\n";
      $body .= _("Best regards") . "\n" . _("CAcert.org Support!") . "\n\n";
      sendmail($user{email}, "[CAcert.org] Your GPG/PGP Key",
        $body, "support\@cacert.org", "", "", "CAcert Support");
    }
    else {
      SysLog("Could not find the issued gpg key. " . $row{"id"} . "\n");
    }
  }
}

# Main program loop

my $crlcheck = 0;

$SIG{INT} = \&signal_handler;
$SIG{TERM} = \&signal_handler;

sub signal_handler {
  LogErrorAndDie("Caught signal $!");
}

while (-f "./client.pl-active") {
  SysLog("Handling GPG database ...\n");
  HandleGPG();
  SysLog("Issueing certs ...\n");
  HandleCerts(0, 0);    #personal client certs
  HandleCerts(0, 1);    #personal server certs
  HandleCerts(1, 0);    #org client certs
  HandleCerts(1, 1);    #org server certs
  SysLog("Revoking certs ...\n");
  RevokeCerts(0, 0);    #personal client certs
  RevokeCerts(0, 1);    #personal server certs
  RevokeCerts(1, 0);    #org client certs
  RevokeCerts(1, 1);    #org server certs

  $crlcheck++;
  RefreshCRLs() if (($crlcheck % 100) == 1);

  my $timestamp = POSIX::strftime("%m%d%H%M%Y.%S", gmtime);
  SysLog("Send NUL request\n");
  Request($ver, 0, 0, 0, 0, 0, 0, 0, $timestamp, "", "");
  SysLog("NUL request sent\n");
  sleep(1);
  usleep(1700000);
}
