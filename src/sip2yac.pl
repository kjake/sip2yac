#!/usr/bin/perl -w
# 1.00 Initial release for MythTV by James Armstrong
# 1.01 Changed Caller ID Name parsing to allow for no name.
#      by Larry Silverman
# 1.02 Reformat phone number to be in format xxx-xxx-xxxx.
#      Enable display of date/time in OSD.
#      Adjust default filter to check port 10000.
#      Reformat perl code.
#      by Kevin Venkiteswaran
# 1.03 First Windows implementation as a YAC Server instead
#      Added option to ignore a phone number since Vonage is sending an invite packet for Outgoing calls as well
#      Commented out all Unix things for now
#      Use WinPcap to enable sniffing
# 1.04 Implemented use of Windows Syslog (Event Viewer)
#      Since Windows has no POSIX interface, it is not possible to fork() (correctly), removed Daemon option
#      Cleaned up print outs
#      by Kevin Jacobson (for v1.03+)
# 1.05 Defined dependant Windows Services hooks
#      Started building exe with Windows Service support
#      Cleaned up Help output
#      Further cleanup of Logging
# 1.06 Changed default sniff port to 5060 to be compliant with more SIP services
#      Changed to only write to the Windows Event log when running as a service
#      Further cleanup of the Help text
#      Set Pcap to only compile the filter if a filter has been set, else just loop through all traffic
#      Changed Help text to use double-quotes to set the Pcap filter, else we set a unterminated string value that causes the script to throw-up
# 1.07 Setup a "fake" fork() to allow the service to start as a parent, spawn child, and poll child and no longer be in a loop so as to catch the STOP from Windows Service control
# 1.08 Should see an 11 digit phone number incoming from the SIP provider and reformat to a 10 digit formatted number
#      Set listener timeout to 5 seconds so the program doesn't wait forever if a listener is off
#      Strip any single or double quotes from the filter string to keep the argument reader from getting confused
# 1.09 Added additional error checking
#      Fixed YAC listener message sending and added sucess/fail debug messages
# 1.10 Added reverse lookup for VoIP systems that do not receive CNAM/CIDNAME
#      Reverse Lookup Code from: http://www.teamforrest.com/blog/89/using-agi-to-get-caller-id-name-cnam/
#      Thanks to 'traker1001' on the SageTV forums for the help!
# 1.11 Lookup missing CNAM/CIDNAME info from CSV file before going to the internet
#      Format: 2125556789,Capt. Crunch
# 1.12 Add additional reverse lookup sources
#      Rename project to sip2yac
# 1.13 Added more comments to source
#      Added logic to prevent duplicate entries from being added to the CSV file
#      Added feature to log outgoing calls to CSV


use IO::Socket;
use IO::Socket::INET;
use Net::Pcap;
use NetPacket::Ethernet qw(:strip);
use NetPacket::IP qw(:strip);
use NetPacket::TCP;
use NetPacket::UDP;
#use Unicode::String qw(utf8 latin1 utf16);
use Sys::Syslog;
use Sys::Syslog::Win32;
use Win32;
use Win32::Process qw(STILL_ACTIVE);
use Win32::File::VersionInfo;
use LWP::UserAgent;
use DBI;

autoflush STDOUT 1;

######################################################################
#########   User Defined Variables                           #########
######################################################################
my ($pid, $child, $all_devs, $notifylist, $debugmsg, @hosts_to_notify);
my $debug=0;
my $debug2=0;
my $quiet=0;
my $dev="*";
my $filter_str="udp and port 5060";
my $user="root";
my $promisc=1;
my $to_ms=1000;
my $useEvtlog=0;
my $log2csv=0;
my $update_csv=0;
my $ignore="";
my $ident="sip2yac";
my $facility="local1";
my $options="pid,perror";
my $priority="info";
my $useragent="Mozilla/5.0 (Windows; U; Windows NT 6.1; en-US) AppleWebKit/534.6 (KHTML, like Gecko) Chrome/6.0.491.0 Safari/534.6";
my $version = GetFileVersionInfo ( PerlSvc::exe() )->{FileVersion};
my $dbh = DBI->connect ("dbi:CSV:", undef, undef, {
        f_schema         => undef,
        f_dir            => ".",
        f_ext            => ".csv/r",
        RaiseError       => 0,
        PrintError       => 0,
});
$dbh->{csv_tables}{sip2yac} = {
        eol         => "\n",
        sep_char    => ",",
        quote_char  => undef,
        escape_char => undef,
        col_names => [qw( cidnum cidname )],
        };
$dbh->{csv_tables}{CallLog} = {
        eol         => "\n",
        sep_char    => ",",
        quote_char  => undef,
        escape_char => undef,
        col_names => [qw( date phonenum phonename )],
        };
$PerlSvc::Config{ServiceName} = "sip2yac";
$PerlSvc::Config{DisplayName} = "sip2yac";
$PerlSvc::Config{StartType} = "auto";
$PerlSvc::Config{StartNow} = 1;
$PerlSvc::Config{Description} = "Sends incoming SIP callerID info to YAC listeners";
######################################################################
#########   End User Defined Variables--Modify nothing below #########
######################################################################

######################################################################
# Child global variables
######################################################################
my $pcap_t;
my $err;
my $count = -1;

### These shouldn't be changed (yet)
my $optimize=0;
my $netmask=0;
my $snaplen=50000;
######################################################################
# End child global variables
######################################################################

print "sip2yac $version (win32 impl. by Kevin Jacobson)\n";

### All PerlSvc:: calls are specific to the ActiveState Perl PDK

#
# Tell the service what to do when issued a 'Start' command
#
sub PerlSvc::Startup() {
	&getOptions(@ARGV) || die "Could not get options\n";
	$useEvtlog=1;
	&open_evtlog();
	log_msg("Running as service...\nSettings for child:\n");
	log_msg("Device: $dev") if (defined($dev) && !($quiet));
	log_msg("WinPcap Filter: $filter_str") if (defined($filter_str) && !($quiet));
	log_msg("Number to ignore: $ignore") if (defined($ignore) && !($quiet));
	log_msg("YAC listeners: $notifylist") if (defined($notifylist) && !($quiet));
	while (PerlSvc::ContinueRun(10)) {
		&launch_proc;
	}
	&ParentLeaveNow();
}

#
# Tell the service what to do when running from the command-line
#
sub PerlSvc::Interactive() {
	&getOptions(@ARGV) || die "Could not get options\n";
	&open_evtlog();
	&start_AS;
	exit;
}

#
# Tell the service what to do when issued a '--install' command
#
sub PerlSvc::Install() {
	if(scalar(@ARGV) > 0 && $ARGV[0]=~/-C=(.*)/){
			$PerlSvc::Config{Parameters} = $ARGV[0];
	}
}

#
# Get the calling thread's last error code (return value)
#
sub ErrorReport {
	log_msg(Win32::GetLastError());
}

#
# Kill spawned process(es)
#
sub kill_child() {
    if (defined($child))
    {
        $child->Kill(0);
        while (!$child->Wait( 1000 )) {
            sleep(1);  # wait for child to exit
        }
    }
}

#
# Stub to handle cleanup when stopping the service
#
sub ParentLeaveNow() {
    kill_child();
    log_msg("Parent exiting...");
    exit;
}

#
# Launching child process from the service
#
sub launch_proc() {
	if (!defined($child)) {
		Win32::Process::Create($child,
									PerlSvc::exe(),
									PerlSvc::exe() . " " . $PerlSvc::Config{Parameters},
									0,
									NORMAL_PRIORITY_CLASS,
									".")|| die ErrorReport();
		$pid = $child->GetProcessID();
		log_msg("Started child process, PID: $pid");
	}
}

#
# Init windows event log for use
#
sub open_evtlog() {
    if ($useEvtlog == 1) {
        Sys::Syslog::openlog $ident, $options, $facility || die "Couldn't open Event Log";
    }
}

#
# Send message to event log if enabled, else console
#
sub log_msg($) {
    my ($msg) = @_;

    if ($useEvtlog == 1){
        Sys::Syslog::syslog($priority, $msg);
    }
    else{
        print $msg . "\n";
    }
}

#
# Main sub
#
sub start_AS {
	log_msg("Starting up...");
	log_msg("Device: $dev") if (defined($dev) && !($quiet));
	log_msg("WinPcap Filter: $filter_str") if (defined($filter_str) && !($quiet));
	log_msg("Number to ignore: $ignore") if (defined($ignore) && !($quiet));
	log_msg("YAC listeners: $notifylist") if (defined($notifylist) && !($quiet));
  # Create CSV file if it doesn't exist
  if (! -e "./sip2yac.csv") {
    $dbh->do ("CREATE TABLE sip2yac (cidnum CHAR (10), cidname CHAR (128))");
  }
  if (! -e "./CallLog.csv" && $log2csv) {
    $dbh->do ("CREATE TABLE CallLog (date CHAR (24), phonenum CHAR (10), phonename CHAR(128))");
  }
  # Test if any network connections exist
	my $pcap_test = Net::Pcap::lookupdev(\$err);
	if (defined $err) { die "\n\nUnable to find any network device.  Make sure WinPcap is installed.\n\n"; }
	
  # Loop thru network interfaces to provide a list to the user
	dev: foreach $_ (Net::Pcap::findalldevs(\$err)) {
		next dev if $_ =~ /Generic/;
		my $net = '';
		my $mask = '';
		my $try_this = '';
    # Only select interfaces that are on a private network
		Net::Pcap::lookupnet($_, \$net, \$mask, \$err);
		if (   (167772160 <= $net && $net <= 184549375)
				|| (2886729728 <= $net && $net <= 2887778303)
				|| (3232235520 <= $net && $net <= 3232301055)
			) { $try_this = " *" };
		$all_devs .= "\n".$_.$try_this;
	}
  
  # Attempt to connect to network interface with lipPcap
	$pcap_t=Net::Pcap::open_live($dev, $snaplen, $promisc, $to_ms, \$err) || die "Error opening libpcap: $err\n\nUse one of the following interfaces (try those with a * first):\n".$all_devs."\n"; #start sniffing
	if ($filter_str ne "") {
		my $filter_t;
		my $result=Net::Pcap::compile($pcap_t, \$filter_t, $filter_str, $optimize, $netmask); #compile filter_str
		Net::Pcap::setfilter($pcap_t, $filter_t); #apply filter
	}
	Net::Pcap::loop($pcap_t, $count, \&process_pkt,"xyz"); #start to process the packets that are received
	return;
}

#
# libPcap packet processing
#
sub process_pkt {
	autoflush STDOUT 1;

	my($pktuser, $hdr, $pkt) = @_;
	if (!defined($hdr) or !defined($pkt)) {
		log_msg("Bad args passed to callback");
		log_msg("Bad user data"), if ($user ne "xyz");
		log_msg("Bad pkthdr"), if (!defined($hdr));
		log_msg("Bad pkt data"), if (!defined($pkt));
		log_msg("not ok");
		exit;
	}
	# get datetimestamp of packet
	my ($sec, $min, $hour, $mday, $mon, $year)=localtime($hdr->{tv_sec});
	$year+=1900;
	$mon+=1;    
	my $datestamp="$year-$mon-$mday $hour:$min:$sec";

	# Strip Ethernet portion of packet off
	my $ip_obj=NetPacket::IP->decode(eth_strip($pkt));
	my $proto=$ip_obj->{proto};
	my ($tcp_obj, $udp_obj, $flags, $dataset) = "";

  # Only prepare UDP traffic since normal SIP traffic is UDP
  # http://www.iana.org/assignments/protocol-numbers/protocol-numbers.xml
	if($proto==17){
		$udp_obj=NetPacket::UDP->decode(ip_strip(eth_strip($pkt)));
		$dataset=$udp_obj->{data};
	} elsif ($debug2) {
		$udp_obj=NetPacket::UDP->decode(ip_strip(eth_strip($pkt)));
		$dataset=$udp_obj->{data};
  }

	# A UDP packet has arrived and has been prepared  
	if (defined($dataset)) {
    print("$dataset\n") if ($debug2);
    $dataset = "INVITE sip: From: \"\" <sip:2125556789@>" if ($debug2);
    # Check to see if UDP traffic was a SIP INVITE message and process
		if ($dataset=~/INVITE sip\:/){
      # Check to see if this is an INCOMING call
			if ($dataset=~/From\:\s*"?(.*)"?\s*<sip\:(.*)@/ && $2 !~ /$ignore/) {
				my $callername = $1;
				my $callernumber = $2;
        my ($npa,$nxx,$station,$name);
				chomp($callername);
				chomp($callernumber);
				$callername=~s/^\s+//g;
				$callername=~s/\s+$//g;
				$callername=~s/\"//g;
				$callernumber=~s/^\s+//g;
				$callernumber=~s/\s+$//g;
				$callernumber=~s/^1//g;
        if ($callernumber =~ /^(\d{3})(\d{3})(\d{4})$/) {
            $npa = $1;
            $nxx = $2;
            $station = $3;
        }
				$callernumber=~s/^(\d{3})(\d{3})(\d{4})$/$1-$2-$3/;
        # Do reverse name lookup if no name was sent by the provider
        if ($callername eq "") {
          log_msg("\nReceived no CNAM/CIDNAME from Telco! Attempting Reverse Lookup...\n");
          my @reversel_providers = qw( csv_lookup anywho_lookup addresses_lookup google_lookup
                                       yp_lookup whitepages_lookup telcod_lookup
                                      );
          foreach $provider (@reversel_providers) {
            last if $callername ne "";
            print("\tTrying $provider...\n") if ($debug);
            $callername = &$provider($npa, $nxx, $station);
            &csv_update ($npa.$nxx.$station, $callername) if ($update_csv);
          }
        }
				log_msg("\nDetected incoming call: $callername $callernumber\n");
        # Format info for YAC
				my $msg = "\@CALL$callername~$callernumber";
				log_msg("YAC message to send: $msg\n");
        
        # Prep list of YAC listeners
				@hosts_to_notify = $notifylist;
				if ($notifylist =~ /\,/) {
					@hosts_to_notify = split(/\,/, $notifylist);
				}
        
        # Send message to defined YAC listeners
				foreach my $host (@hosts_to_notify) {
					my ($notifyaddr,$notifyport) = split(/\:/,$host);
					if (defined($notifyaddr) && defined($notifyport)) {
						log_msg("Connecting to YAC listener at: $notifyaddr:$notifyport\n");
						my $yac_fh = IO::Socket::INET->new(PeerAddr=>$notifyaddr,Proto=>'tcp',PeerPort=>$notifyport,Timeout=>5);
						if ($yac_fh) {
							log_msg("Connected to YAC listener\n");
							print $yac_fh $msg;
							$yac_fh->close;
						} else {
							log_msg("Unable to connect to YAC listener\n");
						}
					}
				}
			}
      $dataset = "INVITE sip: To: <sip:6166989392@>" if ($debug2);
      # Check to see if this is an OUTGOING call
      # Only process if OUTGOING call logging is enabled 
      if ($dataset=~/To\:\s*<sip\:(.*)@/ && $1 !~ /$ignore/ && $log2csv) {
        my $callernumber = $1;
				$callernumber=~s/^\s+//g;
				$callernumber=~s/\s+$//g;
				$callernumber=~s/^1//g;
        log_msg("\nDetected outgoing call: $callernumber\n");
        &logCall($datestamp, $callernumber);
      }
		}
	}
  exit if ($debug2);
	return;
}

#
# Set program options via config file or command line arguments
#
sub getOptions{
    my(@ARGV)=@_;
    my $arg;
    if(scalar(@ARGV) > 0 && $ARGV[0]=~/-C=(.*)/){
        my $configfile=$1;
		log_msg("Config file defined, trying to open: $configfile") if (defined($configfile) && !($quiet));
        open(CONFIG,"$configfile") || log_msg("Error opening config file, using defaults instead.");
        while(<CONFIG>){
            $arg=$_;
            if($arg!~/^\#/){
               $dev=$1 if($arg=~/dev=(.*)/);
               $filter_str=$1 if($arg=~/filter='(.*)'/);
               $update_csv=1 if ($arg=~/updatecsv=1/);
               $log2csv=1 if ($arg=~/logoutgoing=1/);
               $promisc=1 if ($arg=~/promisc=1/);
               $notifylist=$1 if ($arg=~/y=(.*)/);
               $to_ms=$1 if ($arg=~/timeout=(.*)/);
               $quiet=1 if ($arg=~/quiet=1/);
               $debug=$1 if ($arg=~/debug=(.*)/);
               $ignore=$1 if ($arg=~/ignore=(.*)/);
               $useEvtlog=$1 if ($arg=~/useEvtlog=(.*)/);
           }
        }
        close(CONFIG);
    }
    else{
        foreach $arg (@ARGV){
            $dev=$1 if($arg=~/-d=(.*)/);
            $filter_str=$1 if($arg=~/-f=(.*)/);
            $ignore=$1 if($arg=~/-i=(.*)/);
            $update_csv=1 if ($arg=~/-u/);
            $log2csv=1 if ($arg=~/-o/);
            $promisc=1 if ($arg=~/-p/);
            $notifylist=$1 if ($arg=~/-y=(.*)/);
            $to_ms=$1 if ($arg=~/-to=(.*)/);
            $quiet=1 if ($arg=~/--quiet/);
            if($arg=~/--h/ or $arg=~/-h/){
                print "\nTo use:\n";
                print "  --install   Install as a Service\n";
                print "  --remove    Remove the Service\n";
                print "  -C=<file>   Config file to store settings\n";
                print "  -d=<dev>    Specify the device from which packets are captured\n";
                print "  -i=<num>    Specify a phone number to ignore (yours)\n";
                print "  -u          Write any reverse lookup to local CSV\n";
                print "  -o          Log outgoing calls to local CSV\n";
                print "  -f=\"filter\" String to filter on enclosed in single quotes\n";
                print "              (DEFAULT: \"udp and port 5060\")\n";
                print "  -y=ip:port  IP address(es) and port to send YAC messages to (comma separated)\n";
                print "  -p          Place the device into promiscuous mode\n";
                print "  -to=integer Read timeout in ms\n";
                print "  --quiet     Do not print anything but errors to STDOUT\n";
                print "\nDefaults:\n";
                print "  -f=\"udp and port 5060\"\n";
                print "  -p\n";
                print "  -to=1000\n";
                exit;
            }
        }
    }
	$filter_str =~ s/\'|\"//g;
  return 1;
}


sub anywho_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # creste http object with timeout
	my $ua = LWP::UserAgent->new( timeout => 45);
  # create url with phone number
	my $URL = 'http://whitepages.anywho.com/results.php';
  # set browser useragent to try and look like a real browser
	$URL .= qq(?qnpa=$npa&qnpanxx=$npa$nxx&qnxx=$nxx&qp=$nxx$station&qstation=$station);
  # make the connection
	$ua->agent($useragent);
  # store the resulting content
	my $req = new HTTP::Request GET => $URL;
  # process content if we actually got something
	my $res = $ua->request($req);
	if ($res->is_success()) {
		if ($res->content =~ /Find More Information for (.*)<\/a>/) {
			my $clidname = $1;
			return $clidname;
		}
	}
	return "";
}

sub google_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # creste http object with timeout
	my $ua = LWP::UserAgent->new( timeout => 45);
  # create url with phone number
	my $URL = qq(http://www.google.com/search?rls=en&q=phonebook:$npa$nxx$station&ie=UTF-8&oe=UTF-8);
  # set browser useragent to try and look like a real browser
	$ua->agent($useragent);
  # make the connection
	my $req = new HTTP::Request GET => $URL;
  # store the resulting content
	my $res = $ua->request($req);
  # process content if we actually got something
	if ($res->is_success()) {
		if ($res->content =~ /<td>(.+)<td>\(<b>$npa/) {
			my $clidname = $1;
			return $clidname;
		}
	}
	return "";
}

sub whitepages_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # creste http object with timeout
	my $ua = LWP::UserAgent->new( timeout => 45);
  # create url with phone number
	my $URL = qq(http://api.whitepages.com/reverse_phone/1.0/?phone=$npa$nxx$station;api_key=ebbe5c21ae226fdb7d26e1faef45b31e);
  # set browser useragent to try and look like a real browser
	$ua->agent($useragent);
  # make the connection
	my $req = new HTTP::Request GET => $URL;
  # store the resulting content
	my $res = $ua->request($req);
  # process content if we actually got something
	if ($res->is_success()) {
    if ($res->content =~ /<wp:displayname>(.*)<\/wp:displayname>/) {
      $clidname = $1;
      return $clidname;
    }
    if ($res->content =~ /<wp:carrier>(.*)<\/wp:carrier>/) {
      $clidname = $1;
      return $clidname;
    }
	}
	return "";
}

sub addresses_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # creste http object with timeout
	my $ua = LWP::UserAgent->new( timeout => 45);
  # create url with phone number
	my $URL = qq(http://phonenumbers.addresses.com/results.php?ReportType=33&qfilter[pro]=on&qi=0&qk=10&qnpa=$npa&qp=$nxx$station);
  # set browser useragent to try and look like a real browser
	$ua->agent($useragent);
  # make the connection
	my $req = new HTTP::Request GET => $URL;
  # store the resulting content
	my $res = $ua->request($req);
  # process content if we actually got something
	if ($res->is_success()) {
		if ($res->content =~ /<a.*class=\"wp_listing_name\">(.*)<\/a>/) {
			my $clidname = $1;
			return $clidname;
		}
	}
	return "";
}

sub yp_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # creste http object with timeout
	my $ua = LWP::UserAgent->new( timeout => 45);
  # create url with phone number
	my $URL = qq(http://yellowpages.addresses.com/yellow-pages/phone:$npa$nxx$station/listings.html);
  # set browser useragent to try and look like a real browser
	$ua->agent($useragent);
  # make the connection
	my $req = new HTTP::Request GET => $URL;
  # store the resulting content
	my $res = $ua->request($req);
  # process content if we actually got something
	if ($res->is_success()) {
		if ($res->content =~ /<a class=\"listing_name\".*>(.*)<\/a>/) {
			my $clidname = $1;
			return $clidname;
		}
	}
	return "";
}

sub telcod_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # creste http object with timeout
	my $ua = LWP::UserAgent->new( timeout => 45);
  # create url with phone number
	my $URL = qq(http://www.telcodata.us/query/queryexchangexml.html?npa=$npa&nxx=$nxx);
  # set browser useragent to try and look like a real browser
	$ua->agent($useragent);
  # make the connection
	my $req = new HTTP::Request GET => $URL;
  # store the resulting content
	my $res = $ua->request($req);
  # process content if we actually got something
	if ($res->is_success()) {
		if ($res->content =~ /<valid>(.*)<\/valid>/) {
			my $clidname = $1;
      if ($clidname eq "YES") {
				if ($res->content =~ /<ratecenter>(.*)<\/ratecenter>/) {
					$clidname = $1;
					if ($res->content =~ /<state>(.*)<\/state>/) {
						$clidname = $clidname . " $1";
            return $clidname;
					}
				}
      }
		}
	}
	return "";
}

sub csv_lookup {
  # assign arguments
	my ($npa, $nxx, $station) = @_;
  # sql query to csv file
  my $sth = $dbh->prepare (qq;SELECT cidname FROM sip2yac WHERE cidnum = '$npa$nxx$station';);
  $sth->execute();
  # setup column binding
  my $cidname;
  $sth->bind_columns (undef, \$cidname);
  while ($sth->fetch) {
    return $cidname;
  }
  $sth->finish;
	return "";
}

sub csv_update {
  # assign arguments
	my ($cidnum, $cidname) = @_;
  # check to make sure we have a name to save with the number
  if ($cidname ne "") {
    # local variables to split the number into
    my ($npa, $nxx, $station) = "";
    if ($cidnum =~ /^(\d{3})(\d{3})(\d{4})$/) {
      # assign parts of the number if they match the pattern
      $npa = $1;
      $nxx = $2;
      $station = $3;
    }
    # check the csv to see if this number has already been stored
    if (&csv_lookup($npa, $nxx, $station) eq "") {
      # add name and number if the csv lookup returned nothing
      $dbh->do (qq;INSERT INTO sip2yac VALUES('$cidnum','$cidname'););
    }
  }
}

sub logCall {
  # assign arguments
	my ($date, $phonenum) = @_;
  # vars for phone number split
  my ($npa, $nxx, $station) = "";
  if ($phonenum =~ /^(\d{3})(\d{3})(\d{4})$/) {
    # assign parts of the number if they match the pattern
    $npa = $1;
    $nxx = $2;
    $station = $3;
  }
  
  # lookup who is being called
  my $phonename = "";
  my @reversel_providers = qw( csv_lookup anywho_lookup addresses_lookup google_lookup
                               yp_lookup whitepages_lookup telcod_lookup
                              );
  foreach $provider (@reversel_providers) {
    last if $phonename ne "";
    print("\tTrying $provider...\n") if ($debug);
    $phonename = &$provider($npa, $nxx, $station);
    &csv_update ($npa.$nxx.$station, $phonename) if ($update_csv);
  }
  
  # Log call reguardless of whether we have a name
  $dbh->do (qq;INSERT INTO CallLog VALUES('$date','$phonenum','$phonename'););
}