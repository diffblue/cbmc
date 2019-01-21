#!/usr/bin/perl

use subs;
use strict;
use warnings;
use File::Basename;
use Term::ANSIColor;

use Cwd;

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
  my $cmdline = "$cmd $options '$input' >'$output' 2>&1";

  print LOG "Running $cmdline\n";
  system("bash", "-c", "cd '$name' ; $cmdline");
  my $exit_value = $? >> 8;
  my $signal_num = $? & 127;
  my $dumped_core = $? & 128;
  my $failed = 0;

  print LOG "  Exit: $exit_value\n";
  print LOG "  Signal: $signal_num\n";
  print LOG "  Core: $dumped_core\n";

  if($signal_num != 0) {
    print "Killed by signal $signal_num";
    if($dumped_core) {
      print " (code dumped)";
    }
  }

  open my $FH, ">>$name/$output";
  print $FH "EXIT=$exit_value\n";
  print $FH "SIGNAL=$signal_num\n";
  close $FH;

  if($signal_num == 2) {
    print "\nProgram under test interrupted; stopping\n";
    exit 1;
  }

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

sub test($$$$$$$$$$) {
  my ($name, $test, $t_level, $cmd, $ign, $dry_run, $defines, $include_tags, $exclude_tags, $output_suffix) = @_;
  my ($level_and_tags, $input, $options, $grep_options, @results) = load("$test");
  my @keys = keys %{$defines};
  foreach my $key (@keys) {
    my $value = $defines->{$key};
    $options =~ s/(\$$key$|\$$key )/$value /g;
    $options =~ s/\$$key([:;])/$value\1/g; # Variables in --classpath are separated by (semi)colons
  }
  if (scalar @keys) {
    foreach my $word (split(/\s/, $options)) {
      if ((substr($word, 0, 1) cmp '$') == 0) {
        print "$name: variable \"$word\" not replaced; consider passing \"-D$word\"=...";
      }
    }
  }

  my @tags = split(/\s/, $level_and_tags);
  my $level = shift @tags;
  my %tags_set = map { $_ => 1 } @tags;

  # If the user has passes -I (include-tag) or -X (exclude-tag) options, then
  # run the test only if it matches no exclude-tags and either include-tags is
  # not given (implying run all tests) or it matches at least one include-tag.

  my $include_tags_length = @$include_tags;
  my $passes_tag_tests = ($include_tags_length == 0);
  foreach my $include_tag (@$include_tags) {
    if(exists($tags_set{$include_tag})) {
      $passes_tag_tests = 1;
    }
  }

  foreach my $exclude_tag (@$exclude_tags) {
    if(exists($tags_set{$exclude_tag})) {
      $passes_tag_tests = 0;
    }
  }

  # If the 4th line is activate-multi-line-match we enable multi-line checks
  if($grep_options ne "activate-multi-line-match") {
    # No such flag, so we add it back in
    unshift @results, $grep_options;
    $grep_options = "";
  }

  $options =~ s/$ign//g if(defined($ign));

  my $descriptor = basename($test);
  my $output = $descriptor;
  $output =~ s/\.[^.]*$//;
  if($output_suffix) {
    $output .= "-";
    $output .= $output_suffix;
  }
  if(our $opt_f) {
    substr($options, 0, 0) = "$output "
  }
  $output .= ".out";

  if($output eq $input) {
    print("Error in test file -- $test\n");
    return 1;
  }

  print LOG "Test '$name'\n";
  print LOG "  Level: $level\n";
  print LOG "  Input: $input\n";
  print LOG "  Descriptor: $descriptor\n";
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
  if(($level & $t_level) && $passes_tag_tests) {

    if ($dry_run) {
      return 0;
    }

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

          my $dir = getcwd();
          my $abs_path = "$dir/$name/$output";
          open(my $fh => $abs_path) || die "Cannot open '$name/$output': $!";

          # Multi line therefore we run each check across the whole output
          if($grep_options eq "activate-multi-line-match") {
            local $/ = undef;
            binmode $fh;
            my $whole_file = <$fh>;
            $whole_file =~ s/\r\n/\n/g;
            my $is_match = $whole_file =~ /$result/m;
            $r = ($included ? !$is_match : $is_match);
          }
          else
          {
            my $found_line = 0;
            while(my $line = <$fh>) {
              $line =~ s/\r$//;
              if($line =~ /$result/) {
                # We've found the line, therefore if it is included we set
                # the result to 0 (OK) If it is excluded, we set the result
                # to 1 (FAILED)
                $r = !$included;
                $found_line = 1;
                last;
              }
            }

            if($found_line == 0) {
              # None of the lines matched, therefore the result is set to
              # 0 (OK) if and only if the line was not meant to be included
              $r = $included;
            }

          }
          close($fh);


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
    return 2;
  }

  print LOG "\n";

  # if the test is a KNOWNBUG then the test should fail
  my $should_fail = $level eq 8;

  return ($should_fail != $failed);
}

sub dirs() {
  my @list;

  opendir CWD, ".";
  @list = grep { !/^\./ && -d "$_" && !/CVS/ } readdir CWD;
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
             if present, the environment variable TESTPL_JOBS is used as the default
  -n         dry-run: print the tests that would be run, but don't actually run them
  -p         print logs of each failed test (if any)
  -h         show this help and exit
  -C         core: run all essential tests (default if none of C/T/F/K are given)
  -T         thorough: run expensive tests
  -F         future: run checks for future features
  -K         known: run tests associated with known bugs
  -D <key=value> Define - replace \$key string with "value" string in
                 test descriptors
  -I <tag>   run only tests that have the given secondary tag. Can be repeated.
  -X <tag>   exclude tests that have the given secondary tag. Can be repeated.
  -s <suffix>  append <suffix> to all output and log files. Enables concurrent
             testing of the same desc file with different commands or options,
             as runs with different suffixes will operate independently and keep
             independent logs.
  -f         forward the test name to CMD

test.pl expects a test.desc file in each subdirectory. The file test.desc
follows the format specified below. Any line starting with // will be ignored.

<level> [<tag1> [<tag2>...]]
<main source>
<options>
<activate-multi-line-match>
<required patterns>
--
<disallowed patterns>
--
<comment text>

where
  <level>                         is one of CORE, THOROUGH, FUTURE or KNOWNBUG
  <tag1>, <tag2> ... <tagn>       are zero or more space-separated secondary tags, for use with the -I and -X parameters
  <main source>                   is a file with extension .c/.i/.gb/.cpp/.ii/.xml/.class/.jar
  <options>                       additional options to be passed to CMD
  <activate-multi-line-match>     The fourth line can optionally be activate-multi-line-match, if this is the
                                  case then each of the rules will be matched over multiple lines (so can contain)
                                  the new line symbol (\\n) inside them.
  <required patterns>             one or more lines of regualar expressions that must occur in the output
  <disallowed patterns>           one or more lines of expressions that must not occur in output
  <comment text>                  free form text

EOF
  exit 1;
}

use Getopt::Std;
use Getopt::Long qw(:config pass_through bundling);
$main::VERSION = 0.1;
$Getopt::Std::STANDARD_HELP_VERSION = 1;
our ($opt_c, $opt_f, $opt_i, $opt_j, $opt_n, $opt_p, $opt_h, $opt_C, $opt_T, $opt_F, $opt_K, $opt_s, %defines, @include_tags, @exclude_tags); # the variables for getopt
GetOptions("D=s" => \%defines, "X=s" => \@exclude_tags, "I=s" => \@include_tags);
getopts('c:fi:j:nphCTFKs:') or &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
$opt_c or &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
$opt_j = $opt_j || $ENV{'TESTPL_JOBS'} || 0;
if($opt_j && $opt_j != 1 && !$has_thread_pool) {
  warn "Jobs set but thread pool module not found,\n"
   . "install with 'cpan -i Thread::Pool::Simple'\n"
   . "Or avoid setting the -j parameter or the TESTPL_JOBS variable\n";
}
$opt_h and &main::HELP_MESSAGE(\*STDOUT, "", $main::VERSION, "");
my $t_level = 0;
$t_level += 2 if($opt_T);
$t_level += 4 if($opt_F);
$t_level += 8 if($opt_K);
$t_level += 1 if($opt_C || 0 == $t_level);
my $dry_run = $opt_n;
my $log_suffix = $opt_s;

my $logfile_name = "tests";
if($log_suffix) {
  $logfile_name .= "-";
  $logfile_name .= $log_suffix;
}
$logfile_name .= ".log";

open LOG, (">" . $logfile_name);

print "Loading\n";
my @tests = @ARGV != 0 ? @ARGV : dirs();
my $count = 0;
for (@tests){
  my @testfiles = glob "$_/*desc";
  $count += $#testfiles+1;
}
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
  my @files = glob "$test/*.desc";
  for (0..$#files){
    defined($pool) or print "  Running $files[$_]";
    my $start_time = time();
    $failed_skipped = test(
      $test, $files[$_], $t_level, $opt_c, $opt_i, $dry_run, \%defines, \@include_tags, \@exclude_tags, $log_suffix);
    my $runtime = time() - $start_time;

    lock($skips);
    defined($pool) and print "  Running $test $files[$_]";
    if(2 == $failed_skipped) {
      $skips++;
      print "  [SKIPPED]\n";
    } elsif(0 == $failed_skipped) {
      print "  [" . colored("OK", "green") . "] in $runtime seconds\n";
    } else {
      $failures++;
      print "  [" . colored("FAILED", "red") . "]\n";
    }
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

if ($log_suffix) {
  print "Running tests with log suffix: $log_suffix\n";
}
else
{
  print "Running tests\n";
}
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
  print colored("All tests were successful", "green");
} else {
  print colored("Tests failed", "red") . "\n";
  print "  $failures of $count " . (1==$count?"test":"tests") . " failed";
}
print ", $skips " . (1==$skips?"test":"tests") . " skipped" if($skips > 0);
print "\n";


close LOG;

if($opt_p && $failures != 0) {
  open LOG,"<$logfile_name" or die "Failed to open $logfile_name\n";

  my $printed_this_test = 1;
  my $current_test = "";
  my $output_file = "";
  my $descriptor_file = "";

  while (my $line = <LOG>) {
    chomp $line;
    if ($line =~ /^Test '(.+)'/) {
      $current_test = $1;
      $printed_this_test = 0;
    } elsif ($line =~ /Descriptor:\s+([^\s]+)/) {
      $descriptor_file = $1;
    } elsif ($line =~ /Output:\s+([^\s]+)/) {
      $output_file = $1;
    } elsif ($line =~ /\[FAILED\]\s*$/) {
      # print a descriptive header before dumping the test.desc lines that
      # actually weren't matched (and print this header just once)
      if(0 == $printed_this_test) {
        $printed_this_test = 1;
        print "\n\n";
        print "Failed test: $current_test\n";
        open FH, "<$current_test/$output_file";
        while (my $f = <FH>) {
          print $f;
        }
        close FH;
        print "\n\nFailed $descriptor_file lines:\n";
      }

      print "$line\n";
    }
  }
}

exit $failures;
