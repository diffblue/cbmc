#!/bin/bash
# Run regression/cbmc-cpp in the platform set-ups the x86-64 Linux default
# does not cover, before pushing:
#   gcc11  GCC 11's libstdc++ headers (as on Ubuntu 22.04); needs g++-11
#   m32    a 32-bit (i386) cbmc binary: 32-bit long and size_t on the host
#          (configure it with -DCMAKE_C_FLAGS=-m32 -DCMAKE_CXX_FLAGS=-m32)
#   arm64  `--arch arm64' (unsigned char, struct va_list), for the tests
#          that include no system header (the host's headers are x86-64's)
#
# Usage: scripts/platform_check.sh [-b BUILD] [-3 BUILD32] [-j N]
#                                  [gcc11] [m32] [arm64]
# Without set-up names, all available ones run.  Memory per test is capped
# at 8 GB (CBMC_TEST_MEMLIMIT) and time at 900 s.

set -u
REPO="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="$REPO/build"
BUILD32="$REPO/build-32"
JOBS=2
MODES=()
while [ $# -gt 0 ]; do
  case "$1" in
    -b) BUILD="$2"; shift 2 ;;
    -3) BUILD32="$2"; shift 2 ;;
    -j) JOBS="$2"; shift 2 ;;
    gcc11|m32|arm64) MODES+=("$1"); shift ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
[ ${#MODES[@]} -eq 0 ] && MODES=(gcc11 m32 arm64)
# the suite runs in regression/cbmc-cpp: make the build paths absolute
BUILD="$(cd "$BUILD" 2> /dev/null && pwd || echo "$BUILD")"
BUILD32="$(cd "$BUILD32" 2> /dev/null && pwd || echo "$BUILD32")"

export CBMC_TEST_MEMLIMIT=${CBMC_TEST_MEMLIMIT:-8000000}
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$REPO/regression/cbmc-cpp" || exit 2
status=0

# GCC 11 as `gcc'/`g++' for cbmc's preprocessing
gcc11_path() {
  mkdir -p "$TMP/gcc11"
  for t in gcc g++ cpp; do ln -sf "$(command -v $t-11)" "$TMP/gcc11/$t"; done
  echo "$TMP/gcc11"
}

run() {
  local name="$1"; shift
  local log="$TMP/$name.log"
  echo "== $name"
  ../test.pl -e -p -t 900 -j "$JOBS" "$@" > "$log" 2>&1
  local rc=$?
  sed 's/\x1b\[[0-9;]*m//g' "$log" |
    grep -E "^  Running .*\[(FAILED|TIMEOUT)\]|tests? failed|All tests"
  [ $rc -ne 0 ] && status=1
}

for mode in "${MODES[@]}"; do
  case "$mode" in
    gcc11)
      if ! command -v g++-11 > /dev/null; then
        echo "== gcc11: skipped (no g++-11)"; continue
      fi
      PATH="$(gcc11_path):$PATH" run gcc11 \
        -c "$BUILD/bin/cbmc --validate-goto-model --validate-ssa-equation" \
        -C -X libstdcxx12 -X libstdcxx13 -X libstdcxx16 -X libcxx
      ;;
    m32)
      if [ ! -x "$BUILD32/bin/cbmc" ]; then
        echo "== m32: skipped (no $BUILD32/bin/cbmc)"; continue
      fi
      extra=()
      command -v g++-11 > /dev/null && extra=(-X libstdcxx12 -X libstdcxx13)
      run m32 -c "$BUILD32/bin/cbmc" -C -X libstdcxx16 -X libcxx "${extra[@]}"
      ;;
    arm64)
      dirs=()
      for d in */; do
        d="${d%/}"
        grep -qsE '^\s*#\s*include\s*<' "$d"/*.cpp "$d"/*.c && continue
        dirs+=("$d")
      done
      run arm64 -c "$BUILD/bin/cbmc --arch arm64 --validate-goto-model" \
        -C -X libcxx -X libstdcxx16 "${dirs[@]}"
      ;;
  esac
done
exit $status
