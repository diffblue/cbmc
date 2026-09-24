#!/bin/bash
# Runs cbmc --sarif-result on test inputs and validates the SARIF output.
# Usage: test_sarif_valid.sh <cbmc-binary>
# Exit 0 if all validations pass, 1 otherwise.

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CBMC="$1"
FAILED=0
TMPFILE=$(mktemp)
trap 'rm -f "$TMPFILE"' EXIT

for test_case in success failure bounds mixed unknown; do
  case "$test_case" in
    bounds)  OPTS="--bounds-check" ;;
    unknown) OPTS="--stop-on-fail" ;;
    *)       OPTS="" ;;
  esac

  "$CBMC" --sarif-result "$TMPFILE" $OPTS "$SCRIPT_DIR/${test_case}/${test_case}.c" >/dev/null 2>&1 || true
  if ! python3 "$SCRIPT_DIR/validate_sarif.py" "$TMPFILE"; then
    echo "FAILED: ${test_case}.c"
    cat "$TMPFILE"
    FAILED=1
  fi
done

# Test combinations with other UI modes: the normal UI output goes to stdout
# (discarded here) while SARIF is written to a file, which must still be a
# valid SARIF document that actually contains results.
for ui_mode in "--json-ui" "--xml-ui"; do
  "$CBMC" $ui_mode --sarif-result "$TMPFILE" "$SCRIPT_DIR/failure/failure.c" >/dev/null 2>&1 || true
  if ! python3 "$SCRIPT_DIR/validate_sarif.py" "$TMPFILE"; then
    echo "FAILED: failure.c with $ui_mode"
    cat "$TMPFILE"
    FAILED=1
  fi
  if ! grep -q '"ruleId"' "$TMPFILE"; then
    echo "FAILED: $ui_mode combo did not write any SARIF result to the file"
    cat "$TMPFILE"
    FAILED=1
  fi
done

if [ $FAILED -eq 0 ]; then
  echo "All SARIF validation tests passed"
fi
exit $FAILED
