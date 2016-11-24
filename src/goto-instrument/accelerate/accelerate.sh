#!/bin/sh

bindir=`dirname $0`
goto_cc="$bindir/../../goto-cc/goto-cc"
goto_instrument="$bindir/../goto-instrument"
cbmc="$bindir/../../cbmc/cbmc"
cfile=""
cbmcargs=""
ofile=`mktemp`
instrfile=`mktemp`
accfile=`mktemp`

for a in "$@"
do
case $a in
  --*)
    cbmcargs="$cbmcargs $a"
    ;;
  *)
    cfile=$a
   ;;
esac
done

$goto_cc $cfile -o $ofile
$goto_instrument --inline --remove-pointers $ofile $instrfile
timeout 5 $goto_instrument --accelerate $instrfile $accfile
timeout 5 $cbmc --unwind 5 --z3 $cbmcargs $accfile
retcode=$?

#rm -f $ofile $accfile $instrfile

exit $retcode
