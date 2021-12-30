#!/bin/bash

# the script assumes a preinstalled Z3

doalarm () { perl -e 'alarm shift; exec @ARGV' "$@"; killall z3; }

# first, run loopy benchmarks (and compare to etalons) w/o use of memory

for f in l*pdf
do
  ff=${f%.*}
  for suff in "_inv" "_bug"
  do
    echo $ff$suff
    ../../src/goto-cc/goto-cc $ff$suff.c -o test
    ../../src/goto-instrument/goto-instrument --horn --inline --bb test > /dev/null 2>&1
    diff enc.smt2 $ff$suff.smt2 > test
    cat test | wc -l
#    time doalarm 10 z3 $ff$suff.smt2 2>/dev/null
    echo "-----------"
    echo
  done
done

# second, run benchmarks using memory encoding

for f in m*pdf
do
  ff=${f%.*}
  for suff in "_inv" "_bug"
  do
    echo $ff$suff
    ../../src/goto-cc/goto-cc $ff$suff.c -o test
    ../../src/goto-instrument/goto-instrument --horn --inline --bb --mem test > /dev/null 2>&1
    diff enc.smt2 $ff$suff.smt2 > test
    cat test | wc -l
#    time doalarm 10 z3 $ff$suff.smt2 2>/dev/null
    echo "-----------"
    echo
  done
done

# lastly, check for pointer dereferencing

for f in m*pdf
do
  ff=${f%.*}
  for suff in "_inv" "_deref_bug"
  do
    echo $ff$suff
    ../../src/goto-cc/goto-cc $ff$suff.c -o test
    ../../src/goto-instrument/goto-instrument --horn --inline --bb --mem --deref-check test > /dev/null 2>&1
    if [ $suff == "_inv" ]; then diff enc.smt2 $ff"_deref_inv.smt2" > test; fi
    if [ $suff == "_deref_bug" ]; then diff enc.smt2 $ff"_deref_bug.smt2" > test; fi
    cat test | wc -l
#    time doalarm 10 z3 $ff$suff.smt2 2>/dev/null
    echo "-----------"
    echo
  done
done

rm test enc.smt2
