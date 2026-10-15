#!/bin/bash
# Self-test for the irep-copies checker (scripts/check_irep_copies.cpp).
#
# Runs the checker over copy_patterns.cpp and compares its findings against
# expected.txt. This guards both detectors against regressions: the two
# POSITIVE cases must be reported and every NEGATIVE case must stay silent.
#
# Usage: regression/check-irep-copies/run_self_test.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TOOL="$REPO_ROOT/scripts/check-irep-copies"
LLVM_VER=18

if [ ! -x "$TOOL" ]; then
  echo "Building check-irep-copies (clang/LLVM $LLVM_VER)..."
  if ! command -v clang++-$LLVM_VER >/dev/null 2>&1; then
    echo "Error: clang++-$LLVM_VER not found" >&2
    exit 1
  fi
  clang++-$LLVM_VER -o "$TOOL" "$REPO_ROOT/scripts/check_irep_copies.cpp" \
    $(llvm-config-$LLVM_VER --cxxflags | sed 's/-Werror//g') \
    -L/usr/lib/llvm-$LLVM_VER/lib -lclang-cpp \
    $(llvm-config-$LLVM_VER --ldflags --libs --system-libs) \
    -fno-rtti
fi

cd "$SCRIPT_DIR"

ACTUAL=$("$TOOL" copy_patterns.cpp -- -std=c++17 2>&1 |
  grep -E 'warning:.*\[cprover-(unmodified|unnecessary)-irep-copy\]' |
  sed 's|^.*/copy_patterns|copy_patterns|' | sort || true)
EXPECTED=$(grep -vE '^[[:space:]]*(#|$)' expected.txt | sort)

if [ "$ACTUAL" = "$EXPECTED" ]; then
  echo "check-irep-copies self-test passed."
  exit 0
fi

echo "check-irep-copies self-test FAILED." >&2
echo "--- diff (< expected, > actual) ---" >&2
diff <(printf '%s\n' "$EXPECTED") <(printf '%s\n' "$ACTUAL") >&2 || true
exit 1
