#!/bin/bash
# CI script: check for F.16 pass-by-const-reference violations on cheap
# types (C++ Core Guidelines F.16). Uses scripts/check_pass_by_value.cpp
# (Clang LibTooling) and diffs the output against
# scripts/pass_by_value_baseline.txt.
#
# Build directory is taken from the first argument and defaults to "build".
# A compile_commands.json must exist there.
#
# Exit codes:
#   0  no new findings (existing baseline entries may have disappeared,
#      in which case a notice is printed and the user is invited to
#      regenerate the baseline)
#   1  new findings appeared, or the tool failed to build/run
#
# Usage:
#   scripts/run_pass_by_value_check.sh [build-dir]

set -euo pipefail

BUILD_DIR="${1:-build}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TOOL="$SCRIPT_DIR/check-pass-by-value"
BASELINE="$SCRIPT_DIR/pass_by_value_baseline.txt"
SOURCE="$SCRIPT_DIR/check_pass_by_value.cpp"

# ---------------------------------------------------------------------------
# Build the tool if it isn't present or is older than its source.
# ---------------------------------------------------------------------------
if [ ! -x "$TOOL" ] || [ "$SOURCE" -nt "$TOOL" ]; then
  echo "Building check-pass-by-value..."
  LLVM_VER="$(llvm-config --version 2>/dev/null | cut -d. -f1 || echo "")"
  if [ -z "$LLVM_VER" ]; then
    for v in 20 18 15; do
      if command -v "llvm-config-$v" >/dev/null 2>&1; then
        LLVM_VER="$v"
        break
      fi
    done
  fi
  if [ -z "$LLVM_VER" ]; then
    echo "Error: no LLVM installation found" >&2
    exit 1
  fi
  # shellcheck disable=SC2046
  clang++-"$LLVM_VER" -o "$TOOL" "$SOURCE" \
    $(llvm-config-"$LLVM_VER" --cxxflags | sed 's/-Werror//g') \
    -L/usr/lib/llvm-"$LLVM_VER"/lib -lclang-cpp \
    $(llvm-config-"$LLVM_VER" --ldflags --libs --system-libs) \
    -fno-rtti
fi

if [ ! -f "$BUILD_DIR/compile_commands.json" ]; then
  echo "Error: $BUILD_DIR/compile_commands.json not found" >&2
  echo "Run: cmake -S . -B$BUILD_DIR -DCMAKE_EXPORT_COMPILE_COMMANDS=ON" >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Liveness canary: confirm the freshly built tool actually detects a known
# violation. The baseline is empty (zero is the steady state), so without this
# check a broken tool -- missing LLVM, parse failures, every TU bombing out --
# would emit no findings and pass silently. The canary holds exactly one F.16
# violation; it is parsed standalone with `-- -std=c++17`.
# ---------------------------------------------------------------------------
CANARY="$REPO_ROOT/regression/cbmc-pass-by-value/pass_by_value_canary.cpp"
CANARY_FINDINGS="$("$TOOL" "$CANARY" -- -std=c++17 2>/dev/null \
  | grep -c 'cprover-pass-cheap-by-value' || true)"
if [ "$CANARY_FINDINGS" -ne 1 ]; then
  echo "Error: liveness canary expected 1 finding, got $CANARY_FINDINGS." >&2
  echo "The checker is not working correctly; aborting rather than reporting" >&2
  echo "a spurious pass. Check the LLVM toolchain and $CANARY." >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Run the tool over all C++ TUs in src/, jbmc/src/, unit/ and jbmc/unit/, in
# parallel. Each `xargs` worker appends findings to its own per-pid temp file
# (avoiding interleaving); stderr is captured to a sibling .err file so parse
# errors are visible rather than silently dropped. We concatenate at the end.
# ---------------------------------------------------------------------------
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

export TMP TOOL BUILD_DIR
# Per-TU parse errors make the tool return non-zero, which would trip `set -e`
# through `xargs`; tolerate it. Genuine findings are captured via `>>` and
# parse diagnostics via `2>>`; the latter are summarised below.
set +e
find "$REPO_ROOT/src" "$REPO_ROOT/jbmc/src" \
     "$REPO_ROOT/unit" "$REPO_ROOT/jbmc/unit" -name '*.cpp' -print0 \
  | xargs -0 -P "$(nproc)" -n 8 sh -c '
      "$TOOL" -p "$BUILD_DIR/compile_commands.json" "$@" \
        >> "$TMP/$$.out" 2>> "$TMP/$$.err"
    ' _
set -e

# A TU that fails to parse contributes zero findings, so surface the volume of
# parse errors: a spike explains an unexpectedly low finding count.
PARSE_ERRORS="$(cat "$TMP"/*.err 2>/dev/null | grep -c 'error:' || true)"

# Collapse to repo-relative paths so that the baseline is portable.
CURRENT="$TMP/current.txt"
cat "$TMP"/*.out 2>/dev/null \
  | sed "s|$REPO_ROOT/||g" \
  | sort -u > "$CURRENT"

if [ ! -s "$CURRENT" ]; then
  echo "Error: tool produced no output. Check that $BUILD_DIR is built and" >&2
  echo "compile_commands.json is up to date." >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Diff against the baseline.
#   comm -13 baseline current  -> new in current (NEW VIOLATIONS, fail)
#   comm -23 baseline current  -> removed (notice, pass)
# ---------------------------------------------------------------------------
if [ ! -f "$BASELINE" ]; then
  echo "Error: baseline file $BASELINE not found." >&2
  echo "Generate it with:" >&2
  echo "  $0 $BUILD_DIR --regenerate-baseline" >&2
  exit 1
fi

if [ "${2:-}" = "--regenerate-baseline" ]; then
  cp "$CURRENT" "$BASELINE"
  echo "Baseline regenerated at $BASELINE ($(wc -l < "$BASELINE") entries)."
  exit 0
fi

NEW="$TMP/new.txt"
REMOVED="$TMP/removed.txt"
comm -13 <(sort "$BASELINE") "$CURRENT" > "$NEW"
comm -23 <(sort "$BASELINE") "$CURRENT" > "$REMOVED"

NEW_COUNT="$(wc -l < "$NEW")"
REMOVED_COUNT="$(wc -l < "$REMOVED")"
TOTAL_COUNT="$(wc -l < "$CURRENT")"
BASELINE_COUNT="$(wc -l < "$BASELINE")"

echo "Pass-by-value check: $TOTAL_COUNT findings (baseline: $BASELINE_COUNT), \
$PARSE_ERRORS parse-error line(s)."

if [ "$PARSE_ERRORS" -gt 0 ]; then
  echo ""
  echo "Note: $PARSE_ERRORS parse-error line(s) were emitted by the checker;"
  echo "the affected translation units contribute no findings. Sample:"
  # Write the matches to a file and head the file, rather than piping into
  # head: under `set -o pipefail` a `... | grep | head -N` pipeline exits
  # non-zero once head closes the pipe (SIGPIPE / "Broken pipe"), which would
  # abort this script via `set -e` even though the check itself passed.
  grep -h 'error:' "$TMP"/*.err 2>/dev/null > "$TMP/err_sample.txt" || true
  head -5 "$TMP/err_sample.txt"
fi

if [ "$REMOVED_COUNT" -gt 0 ]; then
  echo ""
  echo "Note: $REMOVED_COUNT baseline entries no longer present —"
  echo "consider regenerating the baseline:"
  echo "  $0 $BUILD_DIR --regenerate-baseline"
fi

if [ "$NEW_COUNT" -gt 0 ]; then
  echo ""
  echo "$NEW_COUNT NEW pass-by-value violation(s) found:" >&2
  cat "$NEW" >&2
  echo "" >&2
  echo "These parameters take a cheap-to-copy type by const reference," >&2
  echo "violating C++ Core Guidelines F.16. Pass them by value instead." >&2
  exit 1
fi

echo "No new pass-by-value violations."
exit 0
