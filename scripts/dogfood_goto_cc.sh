#!/usr/bin/env bash
# scripts/dogfood_goto_cc.sh
#
# Dog-fooding harness: compile a curated subset of CBMC's own .cpp
# files with goto-cc, produce a summary of OK / OK_NOISY (errors
# leak but .gb produced) / FAIL / CRASH.
#
# Usage:
#   scripts/dogfood_goto_cc.sh [--baseline] [--expand]
#     --baseline  only run files from DOGFOOD_BASELINE below; PASS
#                 if every file in the baseline is OK_CLEAN.  (Used
#                 as the CI regression target.)
#     --expand    run ALL .cpp files under the DOGFOOD_DIRS directories
#                 (produces a bigger summary but never exits non-zero).
#                 Used to find new bugs during development.  Override
#                 the directory list with DOGFOOD_DIRS="src/a src/b".
#   default behaviour is like --expand but limited to the N smallest
#   files (N=DOGFOOD_SAMPLE_N, default 30).
#
# The script infers the per-file include path from
# build/compile_commands.json.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Files that are expected to compile cleanly with goto-cc.  When any
# of these emits an error or fails to produce a goto binary, the
# script exits non-zero (intended to be the CI gate).
DOGFOOD_BASELINE=(
  "src/util/irep_hash.cpp"
)

# Default sample size when invoked without --baseline or --expand.
DOGFOOD_SAMPLE_N="${DOGFOOD_SAMPLE_N:-30}"

# Directories covered by --expand.  Historically only src/util; widened
# after hand-dog-fooding of goto-conversion and goto-symex sources found
# distinct front-end bugs (std::optional members, decider callers).
DOGFOOD_DIRS="${DOGFOOD_DIRS:-src/util src/goto-programs src/goto-symex src/langapi src/json src/xmllang}"

GOTO_CC="${GOTO_CC:-$REPO_ROOT/build/bin/goto-cc}"
COMPILE_COMMANDS="${COMPILE_COMMANDS:-$REPO_ROOT/build/compile_commands.json}"
TIMEOUT="${TIMEOUT:-60}"

if [ ! -x "$GOTO_CC" ]; then
  echo "error: goto-cc not found at $GOTO_CC (build first?)" >&2
  exit 2
fi
if [ ! -f "$COMPILE_COMMANDS" ]; then
  echo "error: compile_commands.json not found at $COMPILE_COMMANDS" >&2
  echo "run cmake -S . -B build -DCMAKE_EXPORT_COMPILE_COMMANDS=1 first" >&2
  exit 2
fi

mode="default"
case "${1:-}" in
  --baseline) mode="baseline" ;;
  --expand)   mode="expand"   ;;
  "")         mode="default"  ;;
  *)          echo "usage: $0 [--baseline|--expand]" >&2; exit 2 ;;
esac

# Extract the -I flags that CMake uses for cbmc.  Use irep_hash.cpp as
# representative since every util file compiles with the same set.
INCLUDES=$(python3 - <<'PY'
import json, sys
with open("build/compile_commands.json") as f:
    cmds = json.load(f)
for c in cmds:
    if c["file"].endswith("/util/irep_hash.cpp"):
        toks = c["command"].split()
        out = [t for t in toks if t.startswith("-I")]
        print(" ".join(out))
        sys.exit(0)
PY
)

collect_files() {
  local n="$1"
  find $DOGFOOD_DIRS -maxdepth 2 -name '*.cpp' -exec wc -l {} + \
    | sort -n \
    | head -"$n" \
    | awk '{print $2}' \
    | grep -v total
}

case "$mode" in
  baseline)
    files=("${DOGFOOD_BASELINE[@]}")
    ;;
  expand)
    mapfile -t files < <(find $DOGFOOD_DIRS -name '*.cpp' | sort)
    ;;
  *)
    mapfile -t files < <(collect_files "$DOGFOOD_SAMPLE_N")
    ;;
esac

ok_clean=0; ok_noisy=0; fail=0; crash=0
failed_baseline=0
declare -a failures

cd "$REPO_ROOT"

for cpp in "${files[@]}"; do
  rm -f /tmp/dogfood_out.gb
  out=$(timeout "$TIMEOUT" "$GOTO_CC" -std=c++17 $INCLUDES -c "$cpp" \
          -o /tmp/dogfood_out.gb 2>&1)
  exit_code=$?
  has_gb=$([ -f /tmp/dogfood_out.gb ] && echo yes || echo no)
  errors=$(echo "$out" | grep -cE "error:|CONVERSION ERROR|PARSING ERROR")
  if [ $exit_code -eq 139 ] || echo "$out" | grep -q "dumped core"; then
    echo "CRASH    $cpp"
    crash=$((crash+1))
    failures+=("CRASH: $cpp")
    if [ "$mode" = "baseline" ]; then failed_baseline=$((failed_baseline+1)); fi
  elif [ "$has_gb" = "yes" ] && [ "$errors" -eq 0 ]; then
    echo "OK       $cpp"
    ok_clean=$((ok_clean+1))
  elif [ "$has_gb" = "yes" ]; then
    echo "OK_NOISY $cpp ($errors errors)"
    ok_noisy=$((ok_noisy+1))
    if [ "$mode" = "baseline" ]; then failed_baseline=$((failed_baseline+1)); fi
  else
    first=$(echo "$out" | grep -E "error:|CONVERSION ERROR|PARSING ERROR" \
              | head -1 | sed 's|.*error: ||' | cut -c1-70)
    echo "FAIL     $cpp: $first"
    fail=$((fail+1))
    failures+=("FAIL: $cpp")
    if [ "$mode" = "baseline" ]; then failed_baseline=$((failed_baseline+1)); fi
  fi
  rm -f /tmp/dogfood_out.gb
done

total=${#files[@]}
echo ""
echo "Dog-food summary (mode=$mode, $total files)"
echo "  OK (clean):  $ok_clean"
echo "  OK (noisy):  $ok_noisy"
echo "  FAIL:        $fail"
echo "  CRASH:       $crash"

if [ "$mode" = "baseline" ] && [ $failed_baseline -ne 0 ]; then
  echo ""
  echo "BASELINE FAILURES:"
  for f in "${failures[@]}"; do echo "  $f"; done
  exit 1
fi
exit 0
