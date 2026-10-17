#!/usr/bin/env bash

# Preprocess cbmc-cpp tests with the host toolchain so that a failure on a
# CI platform (macOS: Apple libc++) can be reproduced elsewhere from the
# resulting .ii files: `cbmc --os macos <flags from test.desc> test_X.ii'.
#
# usage: preprocess_cpp_tests.sh CBMC OUTDIR [TEST...]
#
# Preprocesses every test that test.pl's logs in regression/cbmc-cpp record
# as failed, and in addition each TEST given (for tests that were excluded,
# or that did not finish before ctest's timeout and so are not in the logs).

set -u

cbmc=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
mkdir -p "$2"
out=$(cd "$2" && pwd)
shift 2
root=$(cd "$(dirname "$0")/.." && pwd)

for hdr in vector iterator; do
  printf '#include <%s>\nint main() {}\n' "$hdr" > "$out/pp_$hdr.cpp"
  "$cbmc" --cpp11 --preprocess "$out/pp_$hdr.cpp" > "$out/$hdr.ii" 2>/dev/null
  rm -f "$out/pp_$hdr.cpp"
done

# test.pl's log: a "Test 'NAME'" block per test, "[FAILED]" lines within
failed=$(awk -v q="'" '/^Test / { t = $2; gsub(q, "", t) } /\[FAILED\]/ { print t }' \
  "$root"/regression/cbmc-cpp/tests*.log 2>/dev/null | sort -u)

for t in $failed "$@"; do
  dir="$root/regression/cbmc-cpp/$t"
  [ -f "$dir/test.desc" ] || continue
  src="$dir/$(sed -n '2p' "$dir/test.desc")"
  [ -f "$src" ] || continue
  flags=$(sed -n '3p' "$dir/test.desc")
  # shellcheck disable=SC2086
  (cd "$dir" && "$cbmc" $flags --preprocess "$src") > "$out/test_$t.ii" 2>/dev/null
done
exit 0
