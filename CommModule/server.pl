#!/usr/bin/perl -w

# (c) 2006-2020 by CAcert.org

# Server (running on the certificate machine)

use strict;
use warnings;
use Device::SerialPort qw(:PARAM :STAT 0.07);
use POSIX;
use IO::Select;
use File::CounterFile;
use Time::HiRes qw(usleep);
use IPC::Open3;
use File::Copy;
use Digest::SHA qw(sha1_hex);

# protocol version:
my $ver = 1;

# debug flag, set to 1 for increased logging, set to 2 to additionally log hexdumps
my $debug = 0;

# enable logging to stdout
my $log_stdout = 1;

# terminate in case of errors
my $paranoid = 1;

my $cps_url  = $ENV{'SIGNER_CPS_URL'}  || "http://www.cacert.org/cps.php";
my $ocsp_url = $ENV{'SIGNER_OCSP_URL'} || "http://ocsp.cacert.org/";

my $gpgbin     = "/usr/bin/gpg";
my $opensslbin = "/usr/bin/openssl";

my $serialport      = $ENV{'SERIAL_PORT'}            || "/dev/ttyUSB0";
my $work            = $ENV{'SIGNER_WORKDIR'}         || './work';
my $ca_conf         = $ENV{'SIGNER_CA_CONFIG'}       || '/etc/ssl';
my $ca_basedir      = $ENV{'SIGNER_BASEDIR'}         || '.';
my $gpg_keyring_dir = $ENV{'SIGNER_GPG_KEYRING_DIR'} || '.';
my $gpg_key_id      = $ENV{'SIGNER_GPG_ID'}          || 'gpg@cacert.org';
my $gpg_cert_digest = $ENV{'SIGNER_GPG_CERT_DIGEST'} || 'SHA256';

my %identity_systems = (
  "1" => 5,    # X.509
  "2" => 1     # OpenPGP
);
my %hashes = (
  "0"  => "",
  "1"  => "-md md5",
  "2"  => "-md sha1",
  "3"  => "-md rmd160",
  "8"  => "-md sha256",
  "9"  => "-md sha384",
  "10" => "-md sha512"
);
my %templates = (
  "0"  => "client.cnf",
  "1"  => "client-org.cnf",
  "2"  => "client-codesign.cnf",
  "3"  => "client-machine.cnf",
  "4"  => "client-ads.cnf",
  "5"  => "server.cnf",
  "6"  => "server-org.cnf",
  "7"  => "server-jabber.cnf",
  "8"  => "ocsp.cnf",
  "9"  => "timestamp.cnf",
  "10" => "proxy.cnf",
  "11" => "subca.cnf"
);

#End of configuration

########################################################

# Global variables
my $start_time  = 5 * 60;       # 5 minutes
my $magic_bytes = "rie4Ech7";
my Device::SerialPort $PortObj;
my IO::Select $sel;

$ENV{'PATH'}            = '/usr/bin/:/bin';
$ENV{'IFS'}             = "\n";
$ENV{'LD_PRELOAD'}      = '';
$ENV{'LD_LIBRARY_PATH'} = '';
$ENV{'LANG'}            = '';

#Logging functions:
sub SysLog($) {
  my $date = POSIX::strftime("%Y-%m-%d", localtime);
  open LOG, ">>logfile$date.txt";
  return if (not defined($_[0]));
  my $timestamp = POSIX::strftime("%Y-%m-%d %H:%M:%S", localtime);
  print LOG "$timestamp $_[0]";
  flush LOG;
  print "$timestamp $_[0]" if ($log_stdout == 1);
  select()->flush();
  close LOG;
}

sub LogErrorAndDie($) {
  SysLog("$_[0]\n");
  if ($paranoid == 1) {
    die $_[0];
  }
}

sub readfile($) {
  my $olds = $/;
  open READIN, "<$_[0]";
  undef $/;
  my $content = <READIN>;
  close READIN;
  $/ = $olds;
  return $content;
}

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
  return substr($len, 1, 3) . $data;
}

#unpack3 unpacks packed data.
sub unpack3($) {
  return undef if ((not defined($_[0])) or length($_[0]) < 3);
  SysLog(sprintf("hexdump: %s\n", hexdump("\x00" . substr($_[0], 0, 3))))
    if ($debug >= 2);
  my $len = unpack("N", "\x00" . substr($_[0], 0, 3));
  SysLog(sprintf(
    "len3: %d length(): %d length()-3: %d\n",
    $len, length($_[0]), (length($_[0]) - 3)
  ))
    if ($debug >= 1);
  return undef if (length($_[0]) - 3 != $len);
  return substr($_[0], 3);
}

#unpack3array extracts a whole array of concatented packed data.
sub unpack3array($) {
  my @retarr = ();
  if ((not defined($_[0])) or length($_[0]) < 3) {
    SysLog("Header data damaged\n");
    return ();
  }
  my $dataleft = $_[0];
  while (length($dataleft) >= 3) {
    SysLog(sprintf("hexdump: %s\n", hexdump("\x00" . substr($dataleft, 0, 3))))
      if ($debug >= 2);
    my $len = unpack("N", "\x00" . substr($dataleft, 0, 3));
    SysLog(sprintf(
      "len3: %d length(): %d length()-3: %d\n",
      $len, length($dataleft), (length($dataleft) - 3)
    ))
      if ($debug >= 1);
    if (length($dataleft) - 3 < $len) {
      SysLog("Data ended prematurely\n");
      return ();
    }
    push @retarr, substr($dataleft, 3, $len);
    $dataleft = substr($dataleft, 3 + $len);
  }
  if (length($dataleft) != 0) {
    SysLog("End of data block missing\n");
    return ();
  }
  return @retarr;
}

sub SerialSettings {
  my $PortObj = $_[0];
  LogErrorAndDie("Could not open Serial Port!") if (!defined($PortObj));
  $PortObj->baudrate(115200);
  $PortObj->parity("none");
  $PortObj->databits(8);
  $PortObj->stopbits(1);
}

#Raw send function over the Serial Interface  (+debugging)
sub SendIt($) {
  return unless defined($_[0]);
  SysLog(sprintf("Sending %d\n",        length($_[0])))  if ($debug >= 1);
  SysLog(sprintf("Bytes to send: %s\n", hexdump($_[0]))) if ($debug >= 2);
  my $data  = $_[0];
  my $total = 0;
  my $mtu   = 30;
  while (length($data)) {
    my $iwrote = scalar($PortObj->write(substr($data, 0, $mtu))) || 0;

    # On Linux, we have to wait to make sure it is being sent, and we dont loose any data.
    usleep(270 * $iwrote + 9000);
    $total += $iwrote;
    $data = substr($data, $iwrote);
    SysLog(sprintf(
      "i wrote: %d total: %d left: %d\n",
      $iwrote, $total, length($data)
    ))
      if ($debug >= 1);
  }
}

#Send data over the Serial Interface with handshaking:
#Warning: This function is implemented paranoid. It exits the program in case something goes wrong.
sub SendHandshakedParanoid($) {
  SysLog("Sending response ...\n") if ($debug >= 1);
  SendIt("\x02");

  LogErrorAndDie("Handshake uncompleted. Connection lost!")
    if (!scalar($sel->can_read(2)));
  usleep(1000000);
  my $data   = "";
  my $length = 0;
  $length = read SER, $data, 1;
  if ($length && $data eq "\x10") {
    SysLog("OK ...\n") if ($debug >= 1);
    my $xor = 0;
    foreach (0 .. length($_[0]) - 1) {
      $xor ^= unpack("C", substr($_[0], $_, 1));
    }

    my $try_again = 1;
    while ($try_again == 1) {
      SendIt($_[0] . pack("C", $xor) . $magic_bytes);

      LogErrorAndDie(
        "Packet receipt was not confirmed in 5 seconds. Connection lost!")
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
        LogErrorAndDie("I cannot send! $length " . unpack("C", $data));
      }
    }

  }
  else {
    SysLog("!Cannot send! $length $data\n");
    LogErrorAndDie("!Stopped sending.");
  }
  SysLog("Done sending response.\n") if ($debug >= 1);
}

sub Receive {
  my $data   = "";
  my @ready  = $sel->can_read(20);
  my $length = read SER, $data, 1, 0;

  SysLog(sprintf("Data: %s\n", hexdump($data))) if ($debug >= 2);

  if ($data eq "\x02") {
    my $modus = 1;
    SysLog("Start received, sending OK\n") if ($debug >= 1);
    SendIt("\x10");

    my $block         = "";
    my $blockfinished = 0;
    my $tries         = 10000;

    while ($blockfinished != 1) {
      LogErrorAndDie("Tried reading too often") if (($tries--) <= 0);

      $data = "";
      if (!scalar($sel->can_read(2))) {
        SysLog("Timeout reading data!\n");
        return;
      }
      $length = read SER, $data, 100, 0;
      if ($length > 0) {
        $block .= $data;
      }
      SysLog(sprintf("Received: %d %d\n", $length, length($block)))
        if ($debug >= 1);
      $blockfinished = defined(unpack3(substr($block, 0, -9))) ? 1 : 0;

      if (!$blockfinished and substr($block, -8, 8) eq $magic_bytes) {
        SysLog("BROKEN Block detected!\n");
        SendIt("\x11");
        $block         = "";
        $blockfinished = 0;
        $tries         = 10000;
      }
    }
    SysLog(sprintf("Block done: %s\n", hexdump($block))) if ($debug >= 2);
    SendIt("\x10");
    SysLog("Returning block\n") if ($debug >= 1);
    return ($block);
  }
  else {
    LogErrorAndDie("Error: No Answer received, Timeout.")
      if (length($data) == 0);
    LogErrorAndDie(sprintf("Error: Wrong Startbyte: %s!", hexdump($data)));
  }

  SysLog("Waiting on next request ...\n");

}

#Checks the CRC of a received block for validity
#Returns 1 upon successful check and 0 for a failure
sub CheckCRC($) {
  my $block = $_[0];
  return 0 if (length($_[0]) < 1);
  return 1 if ($_[0] eq "\x00");
  my $xor = 0;
  foreach (0 .. length($block) - 2) {
    $xor ^= unpack("C", substr($block, $_, 1));
  }
  if ($xor eq unpack("C", substr($block, -1, 1))) {
    return 1;
  }
  else {
    return 0;
  }

}

#Formatting and sending a Response packet
sub Response($$$$$$$) {
  SendHandshakedParanoid(pack3(
        pack3(pack("C*", $_[0], $_[1], $_[2], $_[3]))
      . pack3($_[4])
      . pack3($_[5])
      . pack3($_[6])
  ));
}

#Checks the parameters, whether the certificate system (OpenPGP, X.509, ...) is available,
#whether the specified root key is available, whether the config file is available, ...
#Returns 1 upon success, and dies upon error!
sub CheckSystem($$$$) {
  my ($system, $root, $template, $hash) = @_;
  if (not defined($templates{$template})) {
    LogErrorAndDie("Template unknown!");
  }
  if (not defined($hashes{$hash})) {
    LogErrorAndDie "Hash algorithm unknown!\n";
  }
  if (defined($identity_systems{$system})) {
    if ($root < $identity_systems{$system}) {
      return 1;
    }
    else {
      LogErrorAndDie
        "Identity System $system has only $identity_systems{$system} root keys, key $root does not exist.\n";
    }
  }
  else {
    LogErrorAndDie "Identity system $system not supported";
  }

  return 0;
}

#Selects the specified config file for OpenSSL and makes sure that the specified config file exists
#Returns the full path to the config file
sub X509ConfigFile($$) {
  my ($root, $template) = @_;
  my $opensslcnf = "";
  if ($root == 0) {
    $opensslcnf = "$ca_conf/openssl-$templates{$template}";
  }
  elsif ($root == 1) {
    $opensslcnf = "$ca_conf/class3-$templates{$template}";
  }
  elsif ($root == 2) {
    $opensslcnf = "$ca_conf/class3s-$templates{$template}";
  }
  else {
    $opensslcnf = "$ca_conf/root$root/$templates{$template}";
  }

  # Check that the config file exists
  LogErrorAndDie("Config file does not exist: $opensslcnf!")
    unless (-f $opensslcnf);
  return $opensslcnf;
}

sub CreateWorkspace() {
  mkdir "$work", 0700;
  my $id = (File::CounterFile->new("$work/.counter", "0"))->inc;
  mkdir "$work/" . int($id / 1000), 0700;
  mkdir "$work/" . int($id / 1000) . "/" . ($id % 1000), 0700;
  my $wid = "$work/" . int($id / 1000) . "/" . ($id % 1000);
  SysLog "Creating Working directory: $wid\n";
  return $wid;
}

sub SignX509($$$$$$$$) {
  my ($root, $template, $hash, $days, $spkac, $request, $san, $subject) = @_;

  my $wid = CreateWorkspace();

  my $openssl_config = X509ConfigFile($root, $template);

  SysLog("Subject: $subject\n");
  SysLog("SAN: $san\n");

  $subject =~ s/\\x([A-F0-9]{2})/pack("C", hex($1))/egi;
  $san     =~ s/\\x([A-F0-9]{2})/pack("C", hex($1))/egi;

  LogErrorAndDie("Invalid characters in SubjectAltName!")
    if ($san =~ m/[ \n\r\t\x00#"'\\]/);
  LogErrorAndDie(sprintf(
    "Invalid characters in Subject: %s - %s",
    hexdump($subject), $subject
  ))
    if ($subject =~ m/[\n\r\t\x00#"'\\]/);

  SysLog("Subject: $subject\n");
  SysLog("SAN: $san\n");

  my $x509v3_extensions_file = "";
  if ($templates{$template} =~
    m/server/)  #??? Should we really do that for all and only for server certs?
  {
    open OUT, ">$wid/extfile";
    print OUT "basicConstraints = critical, CA:FALSE\n";
    print OUT
      "keyUsage = critical, digitalSignature, keyEncipherment, keyAgreement\n";
    print OUT "extendedKeyUsage = clientAuth, serverAuth, nsSGC, msSGC\n";
    print OUT "authorityInfoAccess = OCSP;URI:$ocsp_url\n";

    my $crl_url = "";
    if ($root == 0) {
      $crl_url = "http://crl.cacert.org/revoke.crl";
    }
    elsif ($root == 1) {
      $crl_url = "http://crl.cacert.org/class3-revoke.crl";
    }
    elsif ($root == 2) {
      $crl_url = "http://crl.cacert.org/class3s-revoke.crl";
    }
    else {
      $crl_url = "http://crl.cacert.org/root${root}.crl";
    }
    print OUT "crlDistributionPoints = URI:${crl_url}\n";
    print OUT "subjectAltName = $san\n" if (length($san));
    close OUT;
    $x509v3_extensions_file = " -extfile $wid/extfile ";
  }

  my $cmd = ($request =~ m/SPKAC\s*=/) ? "-spkac" : "-subj '$subject' -in";
  if (open OUT, ">$wid/request.csr") {
    print OUT $request;
    close OUT;

    my $command = sprintf(
      "%s ca %s -config %s %s %s/request.csr -out %s/output.crt -days %d -key test -batch %s 2>&1",
      $opensslbin, $hashes{$hash}, $openssl_config, $cmd, $wid, $wid, $days,
      $x509v3_extensions_file);
    my $do = qw/$command/;
    SysLog($do);

    if (open IN, "<$wid/output.crt") {
      undef $/;
      my $content = <IN>;
      close IN;
      $/ = "\n";

      $content =~ s/^.*-----BEGIN/-----BEGIN/s;
      SysLog "Antworte...\n";
      Response($ver, 1, 0, 0, $content, "", "");
      SysLog "Done.\n";
      if ($debug != 0) {
        unlink "$wid/output.crt";
        unlink "$wid/request.csr";
        unlink "$wid/extfile";
      }
    }
    else {
      LogErrorAndDie("Could not read the resulting certificate.");
    }
  }
  else {
    LogErrorAndDie("Could not save request.");
  }
  unlink "$wid";
}

sub SignOpenPGP {
  my ($root, $template, $hash, $days, $spkac, $request, $san, $subject) = @_;

  my $wid = CreateWorkspace();

  my $secring;
  my $pubring;
  if (-d "$gpg_keyring_dir/gpg_root_$root") {
    $secring = "$gpg_keyring_dir/gpg_root_$root/secring.gpg";
    $pubring = "$gpg_keyring_dir/gpg_root_$root/pubring.gpg";
  }
  else {
    $secring = "$gpg_keyring_dir/secring$root.gpg";
    $pubring = "$gpg_keyring_dir/pubring$root.gpg";
  }

  if (!-f $secring || !-f $pubring) {
    LogErrorAndDie("GPG secret key ring $secring not found!");
  }

  copy($secring, "$wid/secring.gpg");
  copy($pubring, "$wid/pubring.gpg");

  my $keyid = undef;

  LogErrorAndDie("Invalid characters in SubjectAltName!")
    if ($san =~ m/[ \n\r\t\x00#"'\\]/);
  LogErrorAndDie("Invalid characters in Subject!")
    if ($subject =~ m/[ \n\r\t\x00#"'\\;]/);

  if (open OUT, ">$wid/request.key") {
    print OUT $request;
    close OUT;

    my $homedir = "$wid/";

    {
      SysLog("Running GnuPG in $homedir...\n");
      my ($stdin, $stdout, $stderr) =
        (IO::Handle->new(), IO::Handle->new(), IO::Handle->new());

      my $command = sprintf(
        "%s --no-tty --homedir %s --command-fd 0 --status-fd 1 --logger-fd 2 --with-colons --import %s/request.key",
        $gpgbin, $homedir, $wid);
      SysLog(sprintf("%s\n", $command)) if ($debug >= 1);

      my $pid = open3($stdin, $stdout, $stderr, $command);
      if ($pid == 0) {
        LogErrorAndDie("Cannot fork GnuPG.");
      }
      $/ = "\n";
      while (<$stdout>) {
        SysLog("Received from GnuPG: $_");
        if (m/^\[GNUPG:\] GOT_IT/) {
        }
        elsif (m/^\[GNUPG:\] GET_BOOL keyedit\.setpref\.okay/) {
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] ALREADY_SIGNED/) {
        }
        elsif (m/^\[GNUPG:\] GOOD_PASSPHRASE/) {
        }
        elsif (m/^\[GNUPG:\] KEYEXPIRED/) {
        }
        elsif (m/^\[GNUPG:\] SIGEXPIRED/) {
        }
        elsif (m/^\[GNUPG:\] IMPORT_OK/) {
        }
        elsif (m/^\[GNUPG:\] IMPORT_RES/) {
        }
        elsif (m/^\[GNUPG:\] IMPORTED ([0-9A-F]{16})/) {
          LogErrorAndDie("More than one OpenPGP sent at once!")
            if (defined($keyid));
          $keyid = $1;
        }
        elsif (m/^\[GNUPG:\] NODATA/) {

          # To crash or not to crash, thats the question.
        }
        else {
          LogErrorAndDie("ERROR: UNKNOWN $_");
        }
      }

      while (<$stderr>) {
        SysLog("Received from GnuPG on stderr: $_");
      }

      waitpid($pid, 0);
    }

    LogErrorAndDie("No KeyID found!") if (!defined($keyid));

    SysLog("Running GnuPG to Sign...\n") if ($debug >= 1);

    {
      my ($stdin, $stdout, $stderr) =
        (IO::Handle->new(), IO::Handle->new(), IO::Handle->new());

      $ENV{'LANG'} = "";

      my $command = sprintf(
        "%s --no-tty --default-key %s --homedir %s --default-cert-expire %dd"
          . " --ask-cert-expire --cert-policy-url %s --command-fd 0 --cert-digest-algo %s"
          . " --status-fd 1 --logger-fd 2 --sign-key %s",
        $gpgbin, $gpg_key_id, $homedir, $days, $cps_url, $gpg_cert_digest,
        $keyid);
      SysLog(sprintf("%s\n", $command)) if ($debug >= 1);

      my $pid = open3($stdin, $stdout, $stderr, $command);

      if ($pid == 0) {
        LogErrorAndDie("Cannot fork GnuPG.");
      }
      SysLog "Got PID $pid\n";
      while (<$stdout>) {
        SysLog("Received from GnuPG: $_");
        if (m/^\[GNUPG:\] GET_BOOL keyedit\.sign_all\.okay/) {
          print $stdin "yes\n";
        }
        elsif (m/^\[GNUPG:\] GOT_IT/) {
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.okay/) {
          print $stdin "yes\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.expire_okay/) {
          print $stdin "yes\n";
        }
        elsif (m/^\[GNUPG:\] GET_LINE siggen\.valid\s?$/) {
          print $stdin "$days\n";
        }
        elsif (m/^\[GNUPG:\] GET_LINE sign_uid\.expire\s?$/) {
          SysLog(
            "DETECTED: Do you want your signature to expire at the same time? (Y/n) -> yes\n"
          );
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.replace_expired_okay/) {
          print $stdin "yes\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.dupe_okay/) {
          print $stdin "yes\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL keyedit\.sign_revoked\.okay/) {
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.revoke_okay/) {
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.expired_okay/) {
          SysLog("The key has already expired!!!\n");
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.nosig_okay/) {
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL sign_uid\.v4_on_v3_okay/) {
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] GET_BOOL keyedit\.setpref\.okay/) {
          print $stdin "no\n";
        }
        elsif (m/^\[GNUPG:\] ALREADY_SIGNED/) {
        }
        elsif (m/^\[GNUPG:\] GOOD_PASSPHRASE/) {
        }
        elsif (m/^\[GNUPG:\] KEYEXPIRED/) {
        }
        elsif (m/^\[GNUPG:\] SIGEXPIRED/) {
        }
        elsif (m/^\[GNUPG:\] NODATA/) {

          # To crash or not to crash, thats the question.
        }
        else {
          LogErrorAndDie("ERROR: UNKNOWN $_");
        }
      }

      while (<$stderr>) {
        SysLog("Received from GnuPG on stderr: $_");
      }

      waitpid($pid, 0);

    }

    SysLog("Running GPG to export...\n");

    my $command;
    my $result;
    $command =
      "$gpgbin --no-tty --homedir $homedir --export --armor $keyid > $wid/result.key";
    SysLog("$command\n") if ($debug >= 1);
    $result = qx/$command/;
    SysLog($result) if ($debug >= 1 || $? != 0);

    $command =
      "$gpgbin --no-tty --homedir $homedir --batch --yes --delete-key $keyid 2>&1";
    SysLog("$command\n") if ($debug >= 1);
    $result = qx/$command/;
    SysLog($result) if ($debug >= 1 || $? != 0);

    if (open IN, "<$wid/result.key") {
      undef $/;
      my $content = <IN>;
      close IN;
      $/ = "\n";

      $content =~ s/^.*-----BEGIN/-----BEGIN/s;
      Response($ver, 2, 0, 0, $content, "", "");

      if ($debug != 0) {
        unlink "$wid/request.key";
        unlink "$wid/result.key";
      }

    }
    else {
      SysLog("NO resulting key found!\n");
    }
  }
  else {
    LogErrorAndDie("Cannot save OpenPGP public key for signing!");
  }

  unlink("$wid/secring.gpg");
  unlink("$wid/pubring.gpg");
  unlink("$wid");
}

sub RevokeX509 {
  my ($root, $template, $hash, $days, $spkac, $request, $san, $subject) = @_;

  LogErrorAndDie("Invalid characters in SubjectAltName!")
    if ($san =~ m/[ \n\r\t\x00#"'\\]/);
  LogErrorAndDie("Invalid characters in Hash!")
    if (!$subject =~ m/^[0-9a-fA-F]+$/);

  SysLog("Revoke X.509 for $root\n");
  SysLog("Current hash from client: $subject\n");

  my $is_current = 0;
  my $current_hash;

  if (-f "revoke-root$root.crl") {
    $current_hash = sha1_hex(readfile("revoke-root$root.crl"));
  }
  else {
    $current_hash = sha1_hex("");
  }

  SysLog("Current hash on signer $current_hash\n");

  if ($subject eq $current_hash) {
    SysLog("Hash matches current CRL.\n");
    SysLog("Deleting old CRLs...\n");
    foreach (<$ca_basedir/currentcrls/$root/*>) {
      if ($_ ne "$ca_basedir/currentcrls/$root/$subject.crl") {
        SysLog("Deleting $_\n");
        unlink $_;
      }
    }
    SysLog("Done with deleting old CRLs.\n");
    if ($subject eq sha1_hex("")) {
      SysLog("Client has empty CRL\n");
    }
    else {
      $is_current = 1;
    }
  }

  my $wid            = CreateWorkspace();
  my $openssl_config = X509ConfigFile($root, $template);

  if (length $request > 0) {
    if (open OUT, ">$wid/request.crt") {
      print OUT $request;
      close OUT;

      my $do;
      my $command;

      $command =
        "$opensslbin ca $hashes{$hash} -config $openssl_config -key test -batch -revoke $wid/request.crt 2>&1";
      $do = `$command`;
      SysLog("output from $command:\n$do") if ($? != 0 || $debug >= 1);
    }
  }

  my $do;
  my $command;
  $command =
    "$opensslbin ca $hashes{$hash} -config $openssl_config -key test -batch -gencrl -crldays 7 -crlexts crl_ext -out $wid/cacert-revoke.crl 2>&1";
  $do = `$command`;
  SysLog("output from $command:\n$do") if ($? != 0 || $debug >= 1);
  $command =
    "$opensslbin crl -inform PEM -in $wid/cacert-revoke.crl -outform DER -out $wid/revoke.crl 2>&1";
  $do = `$command`;
  SysLog("output from $command:\n$do") if ($? != 0 || $debug >= 1);

  unlink "$wid/cacert-revoke.crl";

  SysLog("wrote $wid/revoke.crl\n") if ($debug >= 1);

  if (open IN, "<$wid/revoke.crl") {
    undef $/;
    my $content = <IN>;
    close IN;
    $/ = "\n";
    unlink "$wid/revoke.crl";

    mkdir "$ca_basedir/currentcrls/$root";
    my $new_crl_name =
      sprintf("$ca_basedir/currentcrls/$root/%s.crl", sha1_hex($content));
    open OUT, ">$new_crl_name";
    print OUT $content;
    close OUT;

    if ($is_current == 1) {
      SysLog("Schicke aktuelles Delta...\n");
      my $command =
        "xdelta delta revoke-root$root.crl $new_crl_name delta$root.diff";
      SysLog("$command\n");
      system $command;
      Response($ver, 2, 0, 0, readfile("delta$root.diff"), "", "");
    }
    else {
      if (-f "$ca_basedir/currentcrls/$root/$subject.crl") {
        SysLog("Schicke altes Delta...\n");
        my $command =
          "xdelta delta $ca_basedir/currentcrls/$root/$subject.crl $new_crl_name delta$root.diff";
        SysLog("$command\n");
        system $command;

        Response($ver, 2, 0, 0, readfile("delta$root.diff"), "", "");
      }
      else {
        SysLog("Out of Sync! Sending full CRL...\n");
        Response($ver, 2, 0, 0, readfile($new_crl_name), "", "");
      }
    }

    open OUT, ">revoke-root$root.crl";
    print OUT $content;
    close OUT;

    SysLog("Done.\n");
  }
  else {
    unlink "$wid";
  }
}

sub analyze($) {
  SysLog("Analysiere ...\n") if ($debug >= 1);
  SysLog(hexdump($_[0]) . "\n") if ($debug >= 2);

  my @fields = unpack3array(substr($_[0], 3, -9));
  LogErrorAndDie(sprintf("Wrong number of parameters: %d", scalar(@fields)))
    if (scalar(@fields) != 4);

  SysLog(sprintf("Header: %s\n", hexdump($fields[0]))) if ($debug >= 2);
  my @bytes = unpack("C*", $fields[0]);

  LogErrorAndDie("Header too short!") if (length($fields[0]) < 3);
  LogErrorAndDie(sprintf(
    "Version mismatch. Server does not support version %d, server only supports version %d!",
    $bytes[0], $ver
  ))
    if ($bytes[0] != $ver);
  LogErrorAndDie(sprintf("Header has wrong length: %d! Should be 9 bytes.",
    length($fields[0])))
    if (length($fields[0]) != 9);

  if ($bytes[1] == 0) {
    SysLog("Received NUL request\n");
    if ($fields[1] =~ /^\d+\.\d+$/) {
      open OUT, ">timesync.sh";
      print OUT "date -u '$fields[1]'\n";
      print OUT "hwclock --systohc\n";
      close OUT;
    }
    Response($ver, 0, 0, 0, "", "", "");
    SysLog("Handled NUL request\n");
  }
  elsif ($bytes[1] == 1) {
    SysLog("Received SIGN request\n");
    CheckSystem($bytes[2], $bytes[3], $bytes[4], $bytes[5]);
    if ($bytes[2] == 1) {
      SignX509($bytes[3], $bytes[4], $bytes[5], ($bytes[6] << 8) + $bytes[7],
        $bytes[8], $fields[1], $fields[2], $fields[3]);
    }
    elsif ($bytes[2] == 2) {
      SignOpenPGP($bytes[3], $bytes[4], $bytes[5], ($bytes[6] << 8) + $bytes[7],
        $bytes[8], $fields[1], $fields[2], $fields[3]);
    }
    SysLog("Handled SIGN request\n");
  }
  elsif ($bytes[1] == 2) {
    SysLog("Received REVOKE request\n");
    CheckSystem($bytes[2], $bytes[3], $bytes[4], $bytes[5]);
    if ($bytes[2] == 1) {
      RevokeX509($bytes[3], $bytes[4], $bytes[5], ($bytes[6] << 8) + $bytes[7],
        $bytes[8], $fields[1], $fields[2], $fields[3]);
    }
    SysLog("Handled REVOKE request\n");
  }
  else {
    LogErrorAndDie("Unknown command");
  }
}

# Start of execution
my $timestamp = POSIX::strftime("%Y-%m-%d %H:%M:%S", localtime);
SysLog("Starting Server at $timestamp\n");

mkdir "$work", 0700;
mkdir "$ca_basedir/currentcrls";

SysLog("Opening Serial interface:\n");

#We have to open the SerialPort and close it again, so that we can bind it to a Handle
$PortObj = Device::SerialPort->new($serialport);
SerialSettings($PortObj);
$PortObj->save("serialserver.conf");

undef $PortObj;

$PortObj = tie(*SER, 'Device::SerialPort', "serialserver.conf")
  || LogErrorAndDie("Can't tie using Configuration_File_Name: $!");

LogErrorAndDie("Could not open Serial Interface!") if (not defined($PortObj));
SerialSettings($PortObj);

SysLog("Serial interface opened: $PortObj\n");

#Creating select() selector for improved reading:
$sel = IO::Select->new(\*SER);

$SIG{INT}  = \&signal_handler;
$SIG{TERM} = \&signal_handler;

sub signal_handler {
  LogErrorAndDie("Caught signal $!");
}

SysLog("Server started. Waiting 5 minutes for contact from client ...\n");

#When started, we wait for 5 minutes for the client to connect:
my @ready = $sel->can_read($start_time);

my $count = 0;

#As soon as the client connected successfully, the client has to send a request faster than every 10 seconds
while (@ready = $sel->can_read(15) && -f "./server.pl-active") {
  my $data = "";

  $data = Receive();
  analyze($data);

  $count++;

  SysLog(sprintf(
    "%d requests processed. Waiting on next request ...\n", $count))
    if ($debug >= 1);

}

LogErrorAndDie("Timeout! No data from client anymore!");
