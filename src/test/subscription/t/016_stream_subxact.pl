
# Copyright (c) 2021-2022, PostgreSQL Global Development Group

# Test streaming of large transaction containing large subtransactions
use strict;
use warnings;
use PostgreSQL::Test::Cluster;
use PostgreSQL::Test::Utils;
use Test::More;

# Encapsulate all the common test steps which are related to "streaming"
# parameter so the same code can be run both for the streaming=on and
# streaming=parallel cases.
sub test_streaming
{
	my ($node_publisher, $node_subscriber, $appname) = @_;

	# Insert, update and delete enough rows to exceed 64kB limit.
	$node_publisher->safe_psql(
		'postgres', q{
	BEGIN;
	INSERT INTO test_tab SELECT i, md5(i::text) FROM generate_series(    3,  500) s(i);
	UPDATE test_tab SET b = md5(b) WHERE mod(a,2) = 0;
	DELETE FROM test_tab WHERE mod(a,3) = 0;
	SAVEPOINT s1;
	INSERT INTO test_tab SELECT i, md5(i::text) FROM generate_series(501,  1000) s(i);
	UPDATE test_tab SET b = md5(b) WHERE mod(a,2) = 0;
	DELETE FROM test_tab WHERE mod(a,3) = 0;
	SAVEPOINT s2;
	INSERT INTO test_tab SELECT i, md5(i::text) FROM generate_series(1001,  1500) s(i);
	UPDATE test_tab SET b = md5(b) WHERE mod(a,2) = 0;
	DELETE FROM test_tab WHERE mod(a,3) = 0;
	SAVEPOINT s3;
	INSERT INTO test_tab SELECT i, md5(i::text) FROM generate_series(1501,  2000) s(i);
	UPDATE test_tab SET b = md5(b) WHERE mod(a,2) = 0;
	DELETE FROM test_tab WHERE mod(a,3) = 0;
	SAVEPOINT s4;
	INSERT INTO test_tab SELECT i, md5(i::text) FROM generate_series(2001, 2500) s(i);
	UPDATE test_tab SET b = md5(b) WHERE mod(a,2) = 0;
	DELETE FROM test_tab WHERE mod(a,3) = 0;
	COMMIT;
	});

	$node_publisher->wait_for_catchup($appname);

	my $result =
	  $node_subscriber->safe_psql('postgres',
		"SELECT count(*), count(c), count(d = 999) FROM test_tab");
	is($result, qq(1667|1667|1667),
		'check data was copied to subscriber in streaming mode and extra columns contain local defaults'
	);

	# Cleanup the test data
	$node_publisher->safe_psql('postgres',
		"DELETE FROM test_tab WHERE (a > 2)");
	$node_publisher->wait_for_catchup($appname);
}

# Create publisher node
my $node_publisher = PostgreSQL::Test::Cluster->new('publisher');
$node_publisher->init(allows_streaming => 'logical');
$node_publisher->append_conf('postgresql.conf',
	'logical_decoding_work_mem = 64kB');
$node_publisher->start;

# Create subscriber node
my $node_subscriber = PostgreSQL::Test::Cluster->new('subscriber');
$node_subscriber->init(allows_streaming => 'logical');
$node_subscriber->start;

# Create some preexisting content on publisher
$node_publisher->safe_psql('postgres',
	"CREATE TABLE test_tab (a int primary key, b varchar)");
$node_publisher->safe_psql('postgres',
	"INSERT INTO test_tab VALUES (1, 'foo'), (2, 'bar')");

# Setup structure on subscriber
$node_subscriber->safe_psql('postgres',
	"CREATE TABLE test_tab (a int primary key, b text, c timestamptz DEFAULT now(), d bigint DEFAULT 999)"
);

# Setup logical replication
my $publisher_connstr = $node_publisher->connstr . ' dbname=postgres';
$node_publisher->safe_psql('postgres',
	"CREATE PUBLICATION tap_pub FOR TABLE test_tab");

my $appname = 'tap_sub';

################################
# Test using streaming mode 'on'
################################
$node_subscriber->safe_psql('postgres',
	"CREATE SUBSCRIPTION tap_sub CONNECTION '$publisher_connstr application_name=$appname' PUBLICATION tap_pub WITH (streaming = on)"
);

# Wait for initial table sync to finish
$node_subscriber->wait_for_subscription_sync($node_publisher, $appname);

my $result =
  $node_subscriber->safe_psql('postgres',
	"SELECT count(*), count(c), count(d = 999) FROM test_tab");
is($result, qq(2|2|2), 'check initial data was copied to subscriber');

test_streaming($node_publisher, $node_subscriber, $appname);

######################################
# Test using streaming mode 'parallel'
######################################
my $oldpid = $node_publisher->safe_psql('postgres',
	"SELECT pid FROM pg_stat_replication WHERE application_name = '$appname' AND state = 'streaming';"
);

# "streaming = parallel" does not support non-immutable functions, so change
# the function in the default expression of column "c".
$node_subscriber->safe_psql(
	'postgres', qq{
ALTER TABLE test_tab ALTER COLUMN c SET DEFAULT to_timestamp(0);
ALTER SUBSCRIPTION tap_sub SET(streaming = parallel);
});

$node_publisher->poll_query_until('postgres',
	"SELECT pid != $oldpid FROM pg_stat_replication WHERE application_name = '$appname' AND state = 'streaming';"
  )
  or die
  "Timed out while waiting for apply to restart after changing SUBSCRIPTION";

test_streaming($node_publisher, $node_subscriber, $appname);

$node_subscriber->stop;
$node_publisher->stop;

done_testing();
