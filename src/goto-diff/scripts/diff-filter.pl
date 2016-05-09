#!/usr/bin/perl -w

use strict;

if(scalar(@ARGV)!=3)
{
  print STDERR "syntax: $0 <goto-diff> <old file-or-dir> <new file-or-dir>\n";
  exit(1);
}
my ($diff, $old, $new)=@ARGV;

open DIFF, "<$diff" or die $!;

# goto-diff Input:
#/** main **/
#D        // 0 file data-dep.c line 3 function main
#        signed int cmd;
#+        // 1 file data-dep.c line 4 function main
#        signed int other;
#D        // 2 file data-dep.c line 5 function main
#        signed int other2;
#-        // 2 file data-dep-before.c line 6 function main
#        IF !(other2 != 0) THEN GOTO 1
#+        // 4 file data-dep.c line 8 function main
#        other = 1;
#+        // 5 file data-dep.c line 11 function main
#     1: IF !(other2 != 0) THEN GOTO 2
#D        // 6 file data-dep.c line 13 function main
#        cmd = cmd | 0x4;
#+        // 7 file data-dep.c line 16 function main
#     2: IF !(cmd == 2) THEN GOTO 3
#+        // 8 file data-dep.c line 18 function main
#        other = 3;
#         // 9 file data-dep.c line 21 function main
#     3: return 0;
#         // 10 file data-dep.c line 21 function main
#        dead other2;
#+        // 11 file data-dep.c line 21 function main
#        dead other;
#         // 12 file data-dep.c line 21 function main
#        dead cmd;
#         // 13 file data-dep.c line 21 function main
#        GOTO 4
#         // 14 file data-dep.c line 22 function main
#        dead other2;
#+        // 15 file data-dep.c line 22 function main
#        dead other;
#         // 16 file data-dep.c line 22 function main
#        dead cmd;
#         // 17 file data-dep.c line 22 function main
#     4: END_FUNCTION

my %edits=();

my %edit=();

while(<DIFF>)
{
  chomp;
  my $line=$_;

  if($line =~ /^\/\*\*/ ||
     $line =~ /^\s+\/\/ \d+ file (.*) line (\d+) function \S+$/ ||
     $line =~ /^\s+(\d+:\s+)?(dead |END_FUNCTION).*/)
  {
    %edit=();
  }
  elsif($line =~ /^([\+CD\-cd])\s+\/\/ \d+ file (.*) line (\d+) function \S+$/)
  {
    %edit=( mod => $1, file => $2, line => $3 );
  }
  else
  {
    if(defined($edit{mod}))
    {
      if($edit{mod} =~ /^[\+CD]$/)
      {
        if($edit{mod} eq '+' ||
           !defined($edits{$edit{file}}{$edit{line}}) ||
           $edits{$edit{file}}{$edit{line}} =~ /^[cd]$/)
        {
          $edits{$edit{file}}{$edit{line}}=$edit{mod};
        }
      }
      elsif($edit{mod} =~ /^[\-cd]$/)
      {
        if(!defined($edits{$edit{file}}{$edit{line}}) ||
           ($edit{mod} eq '-' && $edits{$edit{file}}{$edit{line}} =~ /^[cd]$/))
        {
          $edits{$edit{file}}{$edit{line}}=$edit{mod};
        }
      }
      else
      {
        die "Invalid modification $edit{mod}\n";
      }

      %edit=();
    }
  }
}

use File::Temp qw(tempdir);
my $dir=tempdir(CLEANUP => 1);

`cp -a $old $dir/`;
`cp -a $new $dir/`;

foreach my $f (keys(%edits))
{
  my $f_edit="$dir/$f";

  foreach my $l (keys(%{$edits{$f}}))
  {
    if($edits{$f}{$l} =~ /^[CDcd]$/)
    {
      `sed -i '${l}s/^/$edits{$f}{$l}#/' $f_edit`;
    }
  }
}

my @diff_to_clean=split('\n', `cd $dir && diff -urN $old $new`);
my @clean_diff=();
my %rm_lines=();

foreach my $l (@diff_to_clean)
{
  my $push=1;

  if($l =~ /^-([cd])#(.*)/)
  {
    $rm_lines{$2}=1;
    push @clean_diff, "$1$2";
    $push=0;
  }
  elsif($l =~ /^\+(.*)/)
  {
    foreach my $r (keys(%rm_lines))
    {
      if($1 eq $r)
      {
        $push=0;
        delete $rm_lines{$r};
        last;
      }
    }
  }

  push @clean_diff, $l if($push);
}

%rm_lines=();
@diff_to_clean=@clean_diff;
@clean_diff=();

foreach my $l (reverse(@diff_to_clean))
{
  my $unshift=1;

  if($l =~ /^\+([CD])#(.*)/)
  {
    $rm_lines{$2}=1;
    unshift @clean_diff, "$1$2";
    $unshift=0;
  }
  elsif($l =~ /^-(.*)/)
  {
    foreach my $r (keys(%rm_lines))
    {
      if($1 eq $r)
      {
        $unshift=0;
        delete $rm_lines{$r};
        last;
      }
    }
  }

  unshift @clean_diff, $l if($unshift);
}

use Term::ANSIColor;

foreach my $l (@clean_diff)
{
  if($l =~ /^(\s+|---|\+\+\+|@@)/)
  {
    print "$l\n";
  }
  elsif($l =~ /^-/)
  {
    print colored("$l", 'red'), "\n";
  }
  elsif($l =~ /^[cd]/)
  {
    print colored("$l", 'cyan'), "\n";
  }
  elsif($l =~ /^\+/)
  {
    print colored("$l", 'green'), "\n";
  }
  elsif($l =~ /^[CD]/)
  {
    print colored("$l", 'yellow'), "\n";
  }
  else
  {
    die "Invalid diff output $l\n";
  }
}
