#!/bin/bash
# CI script: check for unnecessary irept copies
# Requires: check-irep-moves binary (built from scripts/check_irep_moves.cpp)
# and a compile_commands.json in the build directory.
#
# Usage: scripts/run_irep_copy_check.sh [build-dir]
#
# Returns non-zero if any findings are detected.

set -euo pipefail

BUILD_DIR="${1:-build}"
TOOL="scripts/check-irep-moves"

if [ ! -x "$TOOL" ]; then
  echo "Building check-irep-moves..."
  LLVM_VER=$(llvm-config --version 2>/dev/null | cut -d. -f1 || echo "")
  if [ -z "$LLVM_VER" ]; then
    for v in 20 18 15; do
      if command -v llvm-config-$v >/dev/null 2>&1; then
        LLVM_VER=$v; break
      fi
    done
  fi
  if [ -z "$LLVM_VER" ]; then
    echo "Error: no LLVM installation found" >&2
    exit 1
  fi
  clang++-$LLVM_VER -o "$TOOL" scripts/check_irep_moves.cpp \
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

# Check the hot paths
FINDINGS=$("$TOOL" -p "$BUILD_DIR/compile_commands.json" \
  src/goto-symex/*.cpp \
  src/goto-programs/*.cpp \
  src/ansi-c/goto-conversion/*.cpp \
  src/pointer-analysis/*.cpp \
  src/solvers/flattening/*.cpp \
  2>&1 | grep "warning:" || true)

if [ -n "$FINDINGS" ]; then
  echo "$FINDINGS"
  COUNT=$(echo "$FINDINGS" | wc -l)
  echo ""
  echo "$COUNT unnecessary irept copies found."
  echo "Fix: use 'const auto &' for unmodified copies, 'std::move' for last-use copies."
  exit 1
else
  echo "No unnecessary irept copies found."
  exit 0
fi
