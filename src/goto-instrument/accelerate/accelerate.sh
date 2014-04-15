#!/bin/sh

bindir=`dirname $0`
goto_cc="$bindir/../../goto-cc/goto-cc"
goto_instrument="$bindir/../goto-instrument"
cbmc="$bindir/../../cbmc/cbmc"
cfile=$1
ofile=`mktemp`
accfile=`mktemp`

$goto_cc $cfile -o $ofile
$goto_instrument --accelerate $ofile $accfile
$cbmc --unwind 2 $accfile
retcode=$?

rm $ofile $acfile

exit $?
