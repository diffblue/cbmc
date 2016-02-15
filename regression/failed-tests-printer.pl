#!/usr/bin/perl -w

use strict;

open LOG,"<tests.log" or die "Failed to open tests.log\n";

my $ignore = 1;
my $current_test = "";

while (<LOG>) {
  chomp;
  if (/^Test '(.+)'/) {
    $current_test = $1;
    $ignore = 0;
  } elsif (1 == $ignore) {
    next;
  } elsif (/\[FAILED\]\s*$/) {
    $ignore = 1;
    print "Failed test: $current_test\n";
    my $outf = `sed -n '2p' $current_test/test.desc`;
    $outf =~ s/\..*$/.out/;
    system("cat $current_test/$outf");
    print "\n\n";
  }
}

