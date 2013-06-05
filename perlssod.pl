#!/usr/bin/perl -W
package SSOD;

# Provides a SSO Daemon to enable password synchronization between
# Microsoft's Active Directory and virtually anything.
#
# ZeWaren / Erwan Martin <public@fzwte.net>, http://zewaren.net
# License: MIT

use strict;
use warnings;

use Digest::SHA1  qw(sha1 sha1_hex sha1_base64);
use Crypt::ECB;
use Crypt::DES;
use MIME::Base64 qw(encode_base64);
use Log::Log4perl;
use Net::LDAP;
use Net::LDAP::Extension::SetPassword;
use Config::File;

# Check config every 60 secs
Log::Log4perl::init_and_watch('/etc/pssod/log4perl.conf', 60);
my $log = Log::Log4perl->get_logger("pSSOd");
my $config= Config::File::read_config_file('/etc/pssod/pssod.conf');

my $ssod_secret=     $config->{'ssod_secret'};
my $ssod_tcp_host=   $config->{'ssod_tcp_host'};
my $ssod_tcp_port=   $config->{'ssod_tcp_port'};
my $ssod_debug_mode= $config->{'ssod_debug_mode'};
my $ldap_uri=        $config->{'ldap_uri'};
my $ldap_base=       $config->{'ldap_base'};
my $ldap_binddn=     $config->{'ldap_binddn'};
my $ldap_bindpw=     $config->{'ldap_bindpw'};

my @ldap_servers= split(/, *?/, $ldap_uri);
my $ldap_conn= Net::LDAP->new(\@ldap_servers) or die $log->error("Could not connect to LDAP @ldap_servers");
   $ldap_conn->bind($ldap_binddn, password => $ldap_bindpw) or die $log->error("Could not bind to LDAP as $ldap_binddn");
$log->debug("LDAP-Connection to @ldap_servers established");

if (!$ssod_debug_mode) {
    use base qw(Net::Server::Fork);
}
else {
    use IO::Socket::INET;
}

require perlssod_deskey;

use constant ERROR_SUCCESS => 0;
use constant ERROR_FILE_NOT_FOUND => 1;
use constant ERROR_LOCK_VIOLATION => 2;
use constant ERROR_CANNOT_OPEN_FILE => 3;
use constant ERROR_PASSWORD_NOT_UPDATED => 4;
use constant ERROR_PROTOCOL => 5;
use constant ERROR_BAD_USER_NAME => 6;
use constant ERROR_DECRYPTING => 7;
use constant ERROR_VERSION_NOT_SUPPORTED => 8;
use constant ERROR_BAD_PASSWORD => 9;
use constant ERROR_CANNOT_MAKE_MAPS => 10;
use constant ERROR_WRITE_FAULT => 11;
use constant ERROR_NO_USER_ENTRY => 12;
use constant ERROR_USER_LOGIN_DISABLED => 13;
use constant ERROR_USER_REFUSED => 14;
use constant ERROR_PASSWORD_EXPIRED => 15;
use constant ERROR_PASSWORD_CANT_CHANGE => 16;
use constant ERROR_HISTORY_CONFLICT => 17;
use constant ERROR_TOO_SHORT => 18;
use constant ERROR_TOO_RECENT => 19;
use constant ERROR_BAD_PASSWORD_FILE => 20;
use constant ERROR_BAD_SHADOW_FILE => 21;
use constant ERROR_COMPUTING_LASTCHG_FIELD => 22;
use constant ERROR_VERSION_NUMBER_MISMATCH => 23;
use constant ERROR_PASSWORD_LENGTH_LESS => 24;
use constant ERROR_UPDATE_PASSWORD_FILE => 25;
use constant LAST_ERROR_NUMBER => 25;

#
# is called when a new password change is notified
#
sub data_received_callback {
	my ($username, $password) = @_;

	$log->trace(sprintf("Inside callback with user %s and password %s.", $username, $password));
	if(not defined($username) or 0 == length($username)) {
		$log->error("Received empty username!");
		return ERROR_BAD_USER_NAME;
	}
	if(not defined($password) or 0 == length($password)) {
		$log->error("Received empty password!");
		return ERROR_BAD_PASSWORD;
	}

	my $filter= "(uid=$username)";
	my $user_search_result= $ldap_conn->search(
		base      => $ldap_base,
		filter    => $filter,
		scope     => 'sub',
	);
	if ($user_search_result->is_error and not 32 == $user_search_result->code) {
		$log->error("Error when searching for user $username: " . $user_search_result->error);
		return ERROR_FILE_NOT_FOUND;
	} elsif ( 32 == $user_search_result->code || $user_search_result->count == 0 ) {
		$log->error("The user $username does not exist in LDAP");
		return ERROR_NO_USER_ENTRY;
	} elsif ($user_search_result->count>1) {
		$log->error("The uid $username is not unique. Will not change Password!");
		return ERROR_BAD_USER_NAME;
	} else {
		my $user_entry= $user_search_result->pop_entry;
		my $password_change_result= $ldap_conn->set_password( user => $user_entry->dn, newpasswd => $password );
		if ( $password_change_result->code() ) {
			$log->error("Error when changing password for user $username: " . $password_change_result->error);
			return ERROR_PASSWORD_NOT_UPDATED;
		} else {
			$log->info("Changed password for user $username");
			return ERROR_SUCCESS;
		}
	}
	return ERROR_WRITE_FAULT;
}

#
# htonl
#
sub htonl_ssod {
    my @a = unpack('C*', pack('L', @_));
    return ($a[3]    )|
           ($a[2]<< 8)|
           ($a[1]<<16)|
           ($a[0]<<24);
}

#
# makes the hash from the secret and the two random strings
#
sub make_hash {
    my ($r1, $r2, $secret) = @_;
    my ($sha1, $bytes);

    $sha1 = Digest::SHA1->new;
    $sha1->add_bits($r1, 8*8);
    $sha1->add($secret);
    $sha1->add_bits($r2, 8*8);
    $sha1->add_bits("\x00\x00\x00\x00", 4*8);
    $sha1->add_bits("\x00\x00\x00\x00", 4*8);

    return $sha1->digest;
}

#
# extends the hash to get a 24 byte key
#
sub extend_hash_for_key {
    my ($bytes) = @_;
    my @bytes_a  = split //, $bytes;

    my $h1 = Digest::SHA1->new;
    my $h2 = Digest::SHA1->new;
    my @rgbBuff1 = ("\x36") x 64;
    my @rgbBuff2 = ("\x5C") x 64;

    for my $i (0..19) {
        $rgbBuff1[$i] = $rgbBuff1[$i] ^ $bytes_a[$i];
        $rgbBuff2[$i] = $rgbBuff2[$i] ^ $bytes_a[$i];
    }

    my $rgbBuff1 = pack('A' x 64, @rgbBuff1);
    my $rgbBuff2 = pack('A' x 64, @rgbBuff2);

    $h1->add_bits($rgbBuff1, 64*8);
    $h2->add_bits($rgbBuff2, 64*8);

    my $s1 = $h1->digest;
    my $s2 = $h2->digest;

    my $s = (substr $s1, 0, 20).(substr $s2, 0, 4);
    return $s;
}

#
# generates the checksum
#
sub generate_hash_for_verification {
    my ($KeyTable, $dwVersion, $dwMsgLength, $dwMsgType, $username, $password) = @_;

    my $sha1 = Digest::SHA1->new;
    $sha1->add_bits($KeyTable, 3*32*4*8);
    $sha1->add_bits(pack("L", $dwVersion), 4*8);
    $sha1->add_bits(pack("L", $dwMsgLength), 4*8);
    $sha1->add_bits(pack("L", $dwMsgType), 4*8);
    $sha1->add($username);
    $sha1->add($password);
    return $sha1->digest;
}

#
# triple des
#
sub triple_des_ssod {
    my ($pbIn, $key) = @_;

    my $crypt = Crypt::ECB->new;
    $crypt->padding(PADDING_NONE);
    $crypt->cipher('DES') || die $crypt->errstring;

    $crypt->key(substr($key, 16, 8));
    my $rgbEnc1 = $crypt->decrypt($pbIn);
    $crypt->key(substr($key, 8, 8));
    my $rgbEnc2 = $crypt->encrypt($rgbEnc1);
    $crypt->key(substr($key, 0, 8));
    my $enc = $crypt->decrypt($rgbEnc2);

    return $enc;
}

#
# handle a password change request
#
sub handle_request {
    my ($client_socket) = @_;

    binmode $client_socket;

    $log->debug("Sending random string.");
    my @r1 = ();
    push @r1, int(rand(255)) for (0..7);
    my $r1 = pack('C*', @r1);
    print $client_socket pack("A8", $r1);

    $log->debug("Reading packet.");
    my ($buffer, $version, $message_size, $message);
    read $client_socket, $buffer, 4;
    $version = unpack('N', $buffer);

    if ($version != 0) {
        $log->error("Packet version is unsuported.");
        return ERROR_VERSION_NOT_SUPPORTED;
    }

    read $client_socket, $buffer, 4;
    $message_size = unpack('N', $buffer);

    read $client_socket, $buffer, ($message_size - 8);
    $message = $buffer;

    my( $message_type, $r2, $string ) = unpack( 'N A8 A*', $buffer );

    $log->debug("Computing key.");
    my $h = make_hash $r1, $r2, $ssod_secret;
    my $key = extend_hash_for_key( $h );

    $log->debug("Decrypting buffer.");
    my $count = 0;
    my $decrypted_buffer = '';
    while($count < length($string)) {
        $decrypted_buffer = $decrypted_buffer . triple_des_ssod(substr($string, $count, 8), $key);
        $count = $count + 8;
    }

    my ($username, $password, $message_check_data) = split(/\0/, $decrypted_buffer);

    $log->debug("Checking packet checksum.");
    my @DESTable1 = des_get_key_table(substr($key, 0, 8));
    my @DESTable2 = des_get_key_table(substr($key, 8, 16));
    my @DESTable3 = des_get_key_table(substr($key, 16, 24));
    my @DES3Table;

    push @DES3Table, htonl_ssod($_) foreach (@DESTable1);
    push @DES3Table, htonl_ssod($_) foreach (@DESTable2);
    push @DES3Table, htonl_ssod($_) foreach (@DESTable3);

    $message_size = htonl_ssod($message_size);
    my $message_check_calculated = generate_hash_for_verification(pack('L*', @DES3Table), $version, $message_size, $message_type, $username, $password);

    if (!(encode_base64($message_check_calculated) eq encode_base64($message_check_data))) {
        $log->error(sprintf("Error decrypting packet."));
        return ERROR_DECRYPTING;
    }

    $log->debug(sprintf("Calling callback with user %s.", $username));
    return data_received_callback($username, $password);
}

#
# process a network connection
#
sub process_request {
    my $self = shift;
    my $socket = $self->{server}->{client};

    my $error = handle_request($socket);
    $log->debug(sprintf("Error is %d", $error));

    my $version_number = 0;
    my $message_type = 1;
    my $message_size = 4*4;

    my $response_buffer = pack("N N N N", $version_number, $message_size, $message_type, $error);    
    print $socket $response_buffer;
}

#
# let's rock
#
if (!$ssod_debug_mode) {
    $log->info("Starting pSSOd.");
    SSOD->run(host => $ssod_tcp_host, port => $ssod_tcp_port, ipv => '4');
}
else {
    #Single connection version. Useful for debugging.
    $log->info("Starting pSSOd.");

    my $socket = new IO::Socket::INET (
        LocalHost => $ssod_tcp_host,
        LocalPort => $ssod_tcp_port,
        Proto => 'tcp',
        Listen => 5,
        Reuse => 1
    ) or die "Could not create socket: $!\n";

    my $client_socket = $socket->accept();

    my $error = handle_request $client_socket;
    $log->debug(sprintf("Error is %d", $error));

    my $version_number = 0;
    my $message_type = 1;
    my $message_size = 4*4;

    my $response_buffer = pack("N N N N", $version_number, $message_size, $message_type, $error);    
    print $client_socket $response_buffer;

    while (<$client_socket>) {
        print "some unexpected data arrived\n";
    }

    $socket->close();
}
