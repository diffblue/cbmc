#!/bin/bash
# Runs cbmc --sarif-result on test inputs and validates the SARIF output.
# Usage: test_sarif_valid.sh <cbmc-binary>
# Exit 0 if all validations pass, 1 otherwise.

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CBMC="$1"
FAILED=0
TMPDIR_SARIF=$(mktemp -d)
trap 'rm -rf "$TMPDIR_SARIF"' EXIT

fail()
{
  echo "FAILED: $1"
  [ -f "$2" ] && cat "$2"
  FAILED=1
}

# run_and_validate <name> <expected exit code> <source> <cbmc options...>
run_and_validate()
{
  local name="$1" expected="$2" source="$3"
  shift 3
  local out="$TMPDIR_SARIF/$name.sarif"
  rm -f "$out"
  "$CBMC" --sarif-result "$out" "$@" "$source" >/dev/null 2>&1
  local rc=$?
  if [ "$rc" -ne "$expected" ]; then
    fail "$name: exit code $rc, expected $expected"
  elif [ ! -s "$out" ]; then
    fail "$name: no SARIF output written"
  elif ! python3 "$SCRIPT_DIR/validate_sarif.py" "$out"; then
    fail "$name: invalid SARIF" "$out"
  elif ! grep -q '"ruleId"' "$out"; then
    fail "$name: no SARIF result" "$out"
  fi
}

run_and_validate success 0 "$SCRIPT_DIR/success/success.c"
run_and_validate failure 10 "$SCRIPT_DIR/failure/failure.c"
run_and_validate bounds 10 "$SCRIPT_DIR/bounds/bounds.c" --bounds-check
run_and_validate mixed 10 "$SCRIPT_DIR/mixed/mixed.c"
run_and_validate unknown 10 "$SCRIPT_DIR/unknown/unknown.c" --stop-on-fail

# Combinations with other UI modes: the normal UI output goes to stdout
# (discarded here), while SARIF is written to a file.
run_and_validate json-ui 10 "$SCRIPT_DIR/failure/failure.c" --json-ui
run_and_validate xml-ui 10 "$SCRIPT_DIR/failure/failure.c" --xml-ui

# File names that must be percent-encoded, and absolute paths, which must be
# file: URIs.
mkdir -p "$TMPDIR_SARIF/dir with space"
cp "$SCRIPT_DIR/failure/failure.c" "$TMPDIR_SARIF/dir with space/fäil.c"
run_and_validate path 10 "$TMPDIR_SARIF/dir with space/fäil.c"
if ! grep -q '"uri": "file://.*/dir%20with%20space/f%C3%A4il\.c"' \
  "$TMPDIR_SARIF/path.sarif"; then
  fail "path: unexpected artifact URI" "$TMPDIR_SARIF/path.sarif"
fi

# A file that cannot be written is a usage error, reported before
# verification.
"$CBMC" --sarif-result "$TMPDIR_SARIF/no/such/dir/out.sarif" \
  "$SCRIPT_DIR/failure/failure.c" >"$TMPDIR_SARIF/nodir.log" 2>&1
rc=$?
if [ "$rc" -ne 1 ] || grep -q "Starting Bounded Model Checking" \
  "$TMPDIR_SARIF/nodir.log"; then
  fail "unwritable file: exit code $rc, expected 1 before verification" \
    "$TMPDIR_SARIF/nodir.log"
fi

# Errors while writing are reported. A native Windows binary cannot open
# /dev/full even where the shell provides it.
if [ -w /dev/full ] && [ "${OS:-}" != Windows_NT ]; then
  "$CBMC" --sarif-result /dev/full "$SCRIPT_DIR/success/success.c" \
    >/dev/null 2>&1
  rc=$?
  if [ "$rc" -ne 6 ]; then
    fail "/dev/full: exit code $rc, expected 6"
  fi
fi

# Without verification there are no results to write: warn about this.
"$CBMC" --sarif-result "$TMPDIR_SARIF/show.sarif" --show-properties \
  "$SCRIPT_DIR/failure/failure.c" >"$TMPDIR_SARIF/show.log" 2>&1
if ! grep -q "no verification results were computed" "$TMPDIR_SARIF/show.log"
then
  fail "--show-properties: no warning" "$TMPDIR_SARIF/show.log"
fi

if [ $FAILED -eq 0 ]; then
  echo "All SARIF validation tests passed"
fi
exit $FAILED
