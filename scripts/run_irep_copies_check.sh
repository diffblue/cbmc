#!/bin/bash
# CI script: check for unnecessary irept copies across the whole code base.
#
# Requires: the check-irep-copies binary (built on demand from
# scripts/check_irep_copies.cpp) and a compile_commands.json in the build
# directory.
#
# Usage: scripts/run_irep_copies_check.sh [build-dir]
#
# Every translation unit in compile_commands.json is scanned, excluding the
# unit/ and regression/ test trees (those deliberately copy ireps to exercise
# sharing semantics). Findings listed in the baseline file are known false
# positives and are ignored; the script returns non-zero only for findings
# that are not in the baseline.
#
# To regenerate the baseline after an intentional change, run this script,
# copy the reported findings into scripts/check_irep_copies.baseline, and
# document why each remaining entry is a false positive.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="${1:-build}"
TOOL="$SCRIPT_DIR/check-irep-copies"
BASELINE="$SCRIPT_DIR/check_irep_copies.baseline"

# Pin to clang/LLVM 18 to match the version installed by the CI workflow
# (.github/workflows/syntax-checks.yaml).
LLVM_VER=18

if [ ! -x "$TOOL" ]; then
  echo "Building check-irep-copies (clang/LLVM $LLVM_VER)..."
  if ! command -v clang++-$LLVM_VER >/dev/null 2>&1; then
    echo "Error: clang++-$LLVM_VER not found" >&2
    exit 1
  fi
  clang++-$LLVM_VER -o "$TOOL" "$SCRIPT_DIR/check_irep_copies.cpp" \
    $(llvm-config-$LLVM_VER --cxxflags | sed 's/-Werror//g') \
    -L/usr/lib/llvm-$LLVM_VER/lib -lclang-cpp \
    $(llvm-config-$LLVM_VER --ldflags --libs --system-libs) \
    -fno-rtti
fi

if [ ! -f "$BUILD_DIR/compile_commands.json" ]; then
  echo "Error: $BUILD_DIR/compile_commands.json not found" >&2
  echo "Run: cmake -S . -B$BUILD_DIR -DCMAKE_EXPORT_COMPILE_COMMANDS=ON" >&2
  exit 1
fi

# NOTE: if only `cmake` has been run (no build, as in the CI job), four C/C++
# front-end translation units cannot be parsed because they include headers
# that are generated at build time, and are therefore silently skipped:
#   - src/ansi-c/cprover_library.cpp, src/cpp/cprover_library.cpp
#       (need the generated cprover_library.inc)
#   - src/ansi-c/ansi_c_internal_additions.cpp
#       (needs compiler_headers/gcc_builtin_headers_types.inc)
#   - src/cpp/parse.cpp (needs the bison-generated ansi-c/ansi_c_y.tab.h)
# Build the code (e.g. cmake --build "$BUILD_DIR") before running this script to
# cover them as well.

# All translation units except the unit/ and regression/ test trees.
mapfile -t FILES < <(python3 -c '
import json, sys
for e in json.load(open(sys.argv[1])):
    print(e["file"])
' "$BUILD_DIR/compile_commands.json" | grep -vE '/(unit|regression)/')

echo "Scanning ${#FILES[@]} translation units for unnecessary irept copies..."

# Cap parallelism: each worker runs a full clang parse, so an unbounded -P can
# exhaust memory on machines with many cores.
JOBS="$(nproc)"
[ "$JOBS" -gt 8 ] && JOBS=8

# Findings are emitted on stderr; merge it in and keep only finding lines, with
# the repository root stripped so the output (and baseline) are path-stable.
FINDINGS=$(printf '%s\0' "${FILES[@]}" |
  xargs -0 -P "$JOBS" -n 16 "$TOOL" -p "$BUILD_DIR/compile_commands.json" 2>&1 |
  grep -E 'warning:.*\[cprover-(unmodified|unnecessary)-irep-copy\]' |
  sed "s|$REPO_ROOT/||" | sort -u || true)

if [ -f "$BASELINE" ]; then
  BASELINE_SORTED=$(grep -vE '^[[:space:]]*(#|$)' "$BASELINE" | sort -u)
else
  BASELINE_SORTED=""
fi

NEW=$(comm -23 <(printf '%s\n' "$FINDINGS" | grep -v '^$' || true) \
               <(printf '%s\n' "$BASELINE_SORTED") || true)

if [ -n "$NEW" ]; then
  echo "$NEW"
  echo ""
  echo "$(printf '%s\n' "$NEW" | grep -c .) new unnecessary irept copies found."
  echo "Fix: use 'const auto &' for unmodified copies, 'std::move' for last-use copies."
  echo "If a finding is a verified false positive, add it to scripts/check_irep_copies.baseline."
  exit 1
fi

echo "No new unnecessary irept copies found."
exit 0
