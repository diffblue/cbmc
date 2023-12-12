#!/bin/bash

cleanup()
{
  rm -rf "$target_dir"
}

trap cleanup EXIT

set -e

goto_cc=$1
goto_instrument=$2
cbmc=$3
is_windows=$4
shift 4

cfile=""
cbmcargs=""

# create the temporary directory relative to the current directory, thus
# avoiding file names that start with a "/", which confuses goto-cl (Windows)
# when running in git-bash.
target_dir="$(TMPDIR=. mktemp -d)"

ofile="$target_dir/compiled.gb"
instrfile="$target_dir/instrumented.gb"
accfile="$target_dir/accelerated.gb"

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

if [[ "${is_windows}" == "true" ]]; then
  $goto_cc "$cfile" "/Fe$ofile"
else
  $goto_cc -o "$ofile" "$cfile"
fi

"$goto_instrument" --inline --remove-pointers "$ofile" "$instrfile"
"$goto_instrument" --accelerate "$instrfile" "$accfile"
"$cbmc" --unwind 5 $cbmcargs "$accfile"
