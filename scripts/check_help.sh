#!/bin/bash

set -e

# if a command-line argument is provided, use it as a path to built binaries
# (CMake-style build); otherwise assume we use Makefile-based in-tree build
if [ $# -eq 1 ] ; then
  bin_dir=$(cd $1 ; pwd)
else
  unset bin_dir
fi
echo $bin_dir

# make sure we execute the remainder in the directory containing this script
cd `dirname $0`

missing_options=0

# we don't check goto-cc for now
# we omit crangler for it doesn't take options other than help or a file name
for t in  \
  ../jbmc/src/janalyzer \
  ../jbmc/src/jbmc \
  ../jbmc/src/jdiff \
  ../src/cbmc \
  ../src/goto-analyzer \
  ../src/goto-diff \
  ../src/goto-harness \
  ../src/goto-instrument \
  ../src/memory-analyzer \
  ../src/symtab2gb \
; do
  tool_name=$(basename $t)
  opt_name=$(echo $tool_name | tr 'a-z-' 'A-Z_')
	echo "Extracting the raw list of parameters from $tool_name"
  g++ -E -dM -std=c++11 -I../src -I../jbmc/src $t/*_parse_options.cpp -o macros.c
  # goto-analyzer partly uses the spelling "analyser" within the code base
  echo ${opt_name}_OPTIONS | sed 's/GOTO_ANALYZER/GOTO_ANALYSER/' >> macros.c
  rawstring="`gcc -E -P -w macros.c` \"?h(help)\""
  rm macros.c

  # now the main bit, convert from raw format to a proper list of switches
  cleanstring=`(
    # extract 2-hyphen switches, such as --foo
    # grep for '(foo)' expressions, and then use sed to remove parantheses and
    # put '-' at the start (we accept both --X and -X)
    (echo $rawstring | grep -o "([^)]*)" | sed "s/^.\(.*\).$/-\1/") ;
    # extract 1-hyphen switches, such as -F
    # use sed to remove all (foo) expressions, then you're left with switches
    # and ':', so grep the colons out and then use sed to include the '-'
    (echo $rawstring | sed "s/([^)]*)//g" | grep -o "[a-zA-Z0-9?]" | sed "s/\(.*\)/-\1/")
  ) | sed 's/" "//g'`

  if [ "x$bin_dir" = "x" ] ; then
    tool_bin=$t/$tool_name
  else
    tool_bin=$bin_dir/$tool_name
  fi

  if [ ! -x $tool_bin ] ; then
    echo "$tool_bin is not an executable"
    exit 1
  fi
  $tool_bin --help > help_string

  # some options are intentionally undocumented
  case $tool_name in
    cbmc)
      echo "-all-claims -all-properties -claim -show-claims" >> help_string
      echo "-document-subgoals" >> help_string
      echo "-no-propagation -no-simplify -no-simplify-if" >> help_string
      echo "-floatbv -no-unwinding-assertions" >> help_string
      echo "-slice-by-trace" >> help_string
      ;;
    goto-analyzer)
      echo "-show-intervals -show-non-null" >> help_string
      ;;
    goto-instrument)
      echo "-document-claims-html -document-claims-latex -show-claims" >> help_string
      echo "-no-simplify" >> help_string
      ;;
    janalyzer)
      echo "-show-intervals -show-non-null" >> help_string
      ;;
    jbmc)
      echo "-document-subgoals" >> help_string
      echo "-no-propagation -no-simplify -no-simplify-if" >> help_string
      echo "-no-unwinding-assertions" >> help_string
      ;;
  esac

  for opt in $cleanstring ; do
    if ! grep -q -- $opt help_string ; then
      echo "Option $opt of $tool_name is undocumented"
      missing_options=1
    fi
  done
  rm help_string
done

if [ $missing_options -eq 1 ] ; then
  echo "Undocumented options found"
  exit 1
else
  echo "All options are documented"
  exit 0
fi
