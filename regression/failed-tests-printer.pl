#!/usr/bin/perl -w

use strict;

open LOG,"<tests.log" or die "Failed to open tests.log\n";

my $printed_this_test = 1;
my $current_test = "";

while (<LOG>) {
  chomp;
  if (/^Test '(.+)'/) {
    $current_test = $1;
    $printed_this_test = 0;
  } elsif (/\[FAILED\]\s*$/) {
    if(0 == $printed_this_test) {
      $printed_this_test = 1;
      print "\n\n";
      print "Failed test: $current_test\n";
      my $outf = `sed -n '2p' $current_test/test.desc`;
      $outf =~ s/\..*$/.out/;
      system("cat $current_test/$outf");
      print "\n\nFailed test.desc lines:\n";
    }
    print "$_\n";
  }
}

