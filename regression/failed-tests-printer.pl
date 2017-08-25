#!/usr/bin/perl -w

use strict;

open LOG,"<tests.log" or die "Failed to open tests.log\n";

my $printed_this_test = 1;
my $current_test = "";
my $output_file = "";
my $descriptor_file = "";

while (<LOG>) {
  chomp;
  if (/^Test '(.+)'/) {
    $current_test = $1;
    $printed_this_test = 0;
  } elsif (/Descriptor:\s+([^\s]+)/) {
    $descriptor_file = $1;
  } elsif (/Output:\s+([^\s]+)/) {
    $output_file = $1;
  } elsif (/\[FAILED\]\s*$/) {
    if(0 == $printed_this_test) {
      $printed_this_test = 1;
      print "\n\n";
      print "Failed test: $current_test\n";
      system("cat $current_test/$output_file");
      print "\n\nFailed $descriptor_file lines:\n";
    }
    print "$_\n";
  }
}

