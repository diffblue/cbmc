#!/usr/bin/perl

use subs;
use strict;
use warnings;

my $has_thread_pool = eval
{
  # "http://www.cpan.org/authors/id/J/JW/JWU/Thread-Pool-Simple/Thread-Pool-Simple-0.25.tar.gz"
  # Debian/Ubuntu: libthread-pool-simple-perl
  require Thread::Pool::Simple;
  Thread::Pool::Simple->import();
  1;
};

# test.pl
#
# runs a test and check its output

sub run($$$$$) {
  my ($name, $input, $cmd, $options, $output) = @_;
  my $cmdline = "$cmd $options $input >$output 2>&1";

  print LOG "Running $cmdline\n";
  system("bash", "-c", "cd $name ; $cmdline");
  my $exit_value = $? >> 8;
  my $signal_num = $? & 127;
  my $dumped_core = $? & 128;
  my $failed = 0;

  print LOG "  Exit: $exit_value\n";
  print LOG "  Signal: $signal_num\n";
  print LOG "  Core: $dumped_core\n";

  if($signal_num != 0) {
    $failed = 1;
    print "Killed by signal $signal_num";
    if($dumped_core) {
      print " (code dumped)";
    }
  }

  system "echo EXIT=$exit_value >>$name/$output";
  system "echo SIGNAL=$signal_num >>$name/$output";

  return $failed;
}

sub load($) {
  my ($fname) = @_;

  open FILE, "<$fname";
  my @data = grep { !/^\/\// } <FILE>;
  close FILE;

  chomp @data;
  return @data;
}

sub test($$$$$) {
  my ($name, $test, $t_level, $cmd, $ign) = @_;
  my ($level, $input, $options, @results) = load("$name/$test");
  $options =~ s/$ign//g if(defined($ign));

  my $output = $input;
  $output =~ s/\.(c|i|cpp|ii|xml|class)$/.out/;

  if($output eq $input) {
    print("Error in test file -- $test\n");
    return 1;
  }

  print LOG "Test '$name'\n";
  print LOG "  Level: $level\n";
  print LOG "  Input: $input\n";
  print LOG "  Output: $output\n";
  print LOG "  Options: $options\n";
  print LOG "  Results:\n";
  foreach my $result (@results) {
    print LOG "    $result\n";
  }

  if($level eq "CORE") {
    $level = 1;
  } elsif($level eq "THOROUGH") {
    $level = 2;
  } elsif($level eq "FUTURE") {
    $level = 4;
  } elsif($level eq "KNOWNBUG") {
    $level = 8;
  } else {
    die "Level must be one of CORE, THOROUGH, FUTURE or KNOWNBUG\n";
  }

  my $failed = 2;
  if($level & $t_level) {
    $failed = run($name, $input, $cmd, $options, $output);

    if(!$failed) {
      print LOG "Execution [OK]\n";
      my $included = 1;
      foreach my $result (@results) {
        last if($included == -1);
        if($result eq "--") {
          $included--;
        } else {
          my $r;
          $result =~ s/\\/\\\\/g;
          $result =~ s/([^\\])\$/$1\\r\\\\?\$/;
          system("bash", "-c", "grep \$'$result' '$name/$output' >/dev/null");
          $r = ($included ? $? != 0 : $? == 0);
          if($r) {
            print LOG "$result [FAILED]\n";
            $failed = 1;
          } else {
            print LOG "$result [OK]\n";
          }
        }
      }
    } else {
      print LOG "Execution [FAILED]\n";
    }
  } else {
    print LOG "Execution [SKIPPED]\n";
  }

  print LOG "\n";

  return $failed;
}

sub dirs() {
  my @list;

  opendir CWD, ".";
  @list = grep { !/^\./ && -d "$_" && !/CVS/ && -s "$_/test.desc" } readdir CWD;
  closedir CWD;

  @list = sort @list;

  return @list;
}

sub main::VERSION_MESSAGE($$$$) {
  my ($fh, $getopt, $vers, $opts) = @_;
  print {$fh} << "EOF";
test.pl version $vers -- run a series of regression tests
EOF
}

sub main::HELP_MESSAGE($$$$) {
  my ($fh, $getopt, $vers, $opts) = @_;
  print {$fh} << "EOF";

Usage: test.pl -c CMD [OPTIONS] [DIRECTORIES ...]
  where OPTIONS are one or more options as listed below; one or more directories
  may be passed as arguments to test only those. Otherwise all directories in
  the current location will be used.

  -c CMD     run tests on CMD - required option
  -i <regex> options in test.desc matching the specified perl regex are ignored
  -j <num>   run <num> tests in parallel (requires Thread::Pool::Simple)
  -h         show this help and exit
  -C         core: run all essential tests (default if none of C/T/F/K are given)
  -T         thorough: run expensive tests
  -F         future: run checks for future features
  -K         known: run tests associated with known bugs


test.pl expects a test.desc file in each subdirectory. The file test.desc
follows the format specified below. Any line starting with // will be ignored.

<level>
<main source>
<options>
<required patterns>
--
<disallowed patterns>
--
<comment text>

where
  <level>                is one of CORE, THOROUGH, FUTURE or KNOWNBUG
  <main source>          is a file with extension .c/.i/.cpp/.ii/.xml/.class
  <options>              additional options to be passed to CMD
  <required patterns>    one or more lines of regualar expressions that must occur in the output
  <disallowed patterns>  one or more lines of expressions that must not occur in output
  <comment text>         free form text

EOF
  exit 1;
}

use Getopt::Std;
$main::VERSION = 0.1;
$Getopt::Std::STANDARD_HELP_VERSION = 1;
our ($opt_c, $opt_i, $opt_j, $opt_h, $opt_C, $opt_T, $opt_F, $opt_K); # the variables for getopt
$opt_j = 0;
getopts('c:i:j:hCTFK') or &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
$opt_c or &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
(!$opt_j || $has_thread_pool) or &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
$opt_h and &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
my $t_level = 0;
$t_level += 2 if($opt_T);
$t_level += 4 if($opt_F);
$t_level += 8 if($opt_K);
$t_level += 1 if($opt_C || 0 == $t_level);



open LOG,">tests.log";

print "Loading\n";
my @tests = @ARGV != 0 ? @ARGV : dirs();
my $count = @tests;
print "  $count " . (1==$count?"test":"tests") . " found\n\n";

use Cwd qw(getcwd);
my $cwd = getcwd;
my $failures :shared = 0;
my $skips :shared = 0;
my $pool :shared = undef;

sub do_test($)
{
  my ($test) = @_;
  my $failed_skipped = 0;

  defined($pool) or print "  Running $test";
  $failed_skipped = test($test, "test.desc", $t_level, $opt_c, $opt_i);

  lock($skips);
  defined($pool) and print "  Running $test";
  if(2 == $failed_skipped) {
    $skips++;
    print "  [SKIPPED]\n";
  } elsif(0 == $failed_skipped) {
    print "  [OK]\n";
  } else {
    $failures++;
    print "  [FAILED]\n";
  }
}

if($opt_j>1 && $has_thread_pool && $count>1)
{
  $pool = Thread::Pool::Simple->new(
    min => 2,
    max => $opt_j,
    load => 3,
    do => [\&do_test]
  );
}

print "Running tests\n";
foreach my $test (@tests) {
  if(defined($pool))
  {
    $pool->add($test);
  }
  else
  {
    do_test($test);
  }
}

defined($pool) and $pool->join();

print "\n";

if($failures == 0) {
  print "All tests were successful";
} else {
  print "Tests failed\n";
  print "  $failures of $count " . (1==$count?"test":"tests") . " failed";
}
print ", $skips " . (1==$skips?"test":"tests") . " skipped" if($skips > 0);
print "\n";


close LOG;

exit $failures;

