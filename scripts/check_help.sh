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
  grep '^\\fB\\-' ../doc/man/$tool_name.1 > man_page_opts

  # some options are intentionally undocumented
  case $tool_name in
    cbmc)
      for undoc in \
        -all-claims -all-properties -claim -show-claims \
        -document-subgoals \
        -no-propagation -no-simplify \
        -floatbv -no-unwinding-assertions \
        -slice-by-trace ; do
        echo "$undoc" >> help_string
        echo "$undoc" | sed 's/^/\\fB/;s/-/\\-/g;s/$/\\fR/' >> man_page_opts
      done
      ;;
    goto-analyzer)
      for undoc in -show-intervals -show-non-null ; do
        echo "$undoc" >> help_string
        echo "$undoc" | sed 's/^/\\fB/;s/-/\\-/g;s/$/\\fR/' >> man_page_opts
      done
      ;;
    goto-instrument)
      for undoc in \
        -document-claims-html -document-claims-latex -show-claims \
        -no-simplify ; do
        echo "$undoc" >> help_string
        echo "$undoc" | sed 's/^/\\fB/;s/-/\\-/g;s/$/\\fR/' >> man_page_opts
      done
      ;;
    janalyzer)
      # -jar, -gb are documented, but in a different format
      for undoc in -show-intervals -show-non-null -jar -gb ; do
        echo "$undoc" >> help_string
        echo "$undoc" | sed 's/^/\\fB/;s/-/\\-/g;s/$/\\fR/' >> man_page_opts
      done
      ;;
    jbmc)
      # -jar, -gb are documented, but in a different format
      for undoc in \
        -document-subgoals \
        -no-propagation -no-simplify \
        -no-unwinding-assertions \
        -jar -gb ; do
        echo "$undoc" >> help_string
        echo "$undoc" | sed 's/^/\\fB/;s/-/\\-/g;s/$/\\fR/' >> man_page_opts
      done
      ;;
  esac

  for opt in $cleanstring ; do
    if ! grep -q -- $opt help_string ; then
      echo "Option $opt of $tool_name is undocumented"
      missing_options=1
    fi
    case $opt in
      -help|-h|-?) continue ;;
      -version) continue ;;
    esac
    m_opt=$(echo $opt | sed 's/-/\\\\-/g')
    if ! grep -q -- "$m_opt" man_page_opts ; then
      echo "Option $opt of $tool_name is missing from its man page"
      missing_options=1
    fi
  done
  rm help_string
  rm man_page_opts
done

if [ $missing_options -eq 1 ] ; then
  echo "Undocumented options found"
  exit 1
else
  echo "All options are documented"
  exit 0
fi
