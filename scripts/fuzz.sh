#!/usr/bin/env bash
#
# This script fuzzes two input surfaces of CBMC by mutating the inputs of
# existing regression tests:
# 1. C source code, which is passed to cbmc.
# 2. JSON symbol tables, which are passed to symtab2gb.
#
# The intent is to find crashes, in particular memory-safety problems that only
# a sanitizer build reports. The binaries under test are therefore expected to
# have been built with, e.g., -fsanitize=address,undefined; the script works
# with a plain build as well, but then only detects outright crashes.
#
# Mutation is driven by $RANDOM, which is seeded from a single random seed so
# that a run can be repeated exactly. The seed is printed at the start of every
# run, and again together with the offending input whenever a crash is found.
#
# The number "N" of mutants to try per input surface can be given as the first
# command-line argument; the default is 100. A random seed can be given as the
# second argument to repeat an earlier run.
#
# cbmc and symtab2gb must be found via the system PATH.

set -e

workdir=$(mktemp -d fuzz.XXX)
basedir=$PWD
seed=

print_seed() {
  echo "Random seed being used: $seed"
  echo "To repeat this run: scripts/fuzz.sh $N $seed"
  echo "Fuzzing working directory: $workdir"
}

# Sanitizer configuration: abort on the first report so that the exit status
# tells us a problem was found, and print a stack trace for undefined
# behaviour.
export ASAN_OPTIONS="${ASAN_OPTIONS:-abort_on_error=1:detect_leaks=0}"
export UBSAN_OPTIONS="${UBSAN_OPTIONS:-print_stacktrace=1:halt_on_error=1}"

# Build a mutant of $1 in $2. All choices derive from $RANDOM, which is seeded
# once per run.
mutate() {
  local src=$1
  local dst=$2
  local size
  size=$(wc -c < "$src")

  case $((RANDOM % 4)) in
    0) # splice in random bytes
      local pos=$((RANDOM % (size + 1)))
      head -c "$pos" "$src" > "$dst"
      head -c $((RANDOM % 16 + 1)) /dev/urandom >> "$dst"
      tail -c "+$((pos + 1))" "$src" >> "$dst"
      ;;
    1) # delete a range
      local pos=$((RANDOM % (size + 1)))
      local len=$((RANDOM % 32 + 1))
      head -c "$pos" "$src" > "$dst"
      tail -c "+$((pos + len + 1))" "$src" >> "$dst" || true
      ;;
    2) # truncate
      head -c $((RANDOM % (size + 1))) "$src" > "$dst"
      ;;
    3) # duplicate a range, which tends to produce deeply nested input
      local pos=$((RANDOM % (size + 1)))
      local len=$((RANDOM % 64 + 1))
      head -c "$pos" "$src" > "$dst"
      tail -c "+$((pos + 1))" "$src" | head -c "$len" >> "$dst"
      tail -c "+$((pos + 1))" "$src" >> "$dst"
      ;;
  esac
}

# Run $1 (a command) on the mutant $2. A finding is either a sanitizer report
# or termination by a signal: exit status 128 or above, which includes the abort
# that a sanitizer report triggers with abort_on_error=1. Non-zero exit statuses
# below that are expected, as a mutant is usually not a well-formed input.
#
# A finding is reported only when it reproduces, because a sanitizer build may
# terminate without a diagnostic for reasons outside the program under test.
run_mutant() {
  local what=$1
  local input=$2
  shift 2

  local ec=0
  "$@" > output.txt 2>&1 || ec=$?

  # 124 is the timeout we impose ourselves, and is not a finding.
  if [ $ec -eq 124 ] || { [ $ec -lt 128 ] && ! grep -q "ERROR: AddressSanitizer\|runtime error:" output.txt ; } ; then
    return 0
  fi

  cp "$input" "$basedir/fuzz-crash-$(basename "$input")"

  local confirmed=0
  local i
  for i in 1 2 3 ; do
    local ec2=0
    "$@" > repeat.txt 2>&1 || ec2=$?
    if [ $ec2 -ge 128 ] || grep -q "ERROR: AddressSanitizer\|runtime error:" repeat.txt ; then
      confirmed=1
      break
    fi
  done

  if [ $confirmed -eq 0 ] ; then
    echo "Unconfirmed one-off failure of $what (exit status $ec), continuing;"
    echo "input saved as fuzz-crash-$(basename "$input")"
    return 0
  fi

  echo "CRASH: $what terminated with exit status $ec on mutant $input"
  echo "--- output"
  cat output.txt
  echo "--- input"
  cat "$input"
  print_seed
  echo "Input saved as fuzz-crash-$(basename "$input")"
  return 1
}

fuzz_c() {
  local n=$1
  local -a seeds
  mapfile -t seeds < <(find "$basedir/regression/cbmc" -name main.c | sort)
  echo "Fuzzing the C front end with $n mutants of ${#seeds[@]} inputs"

  for ((i = 0; i < n; ++i)); do
    mutate "${seeds[$((RANDOM % ${#seeds[@]}))]}" mutant.c
    run_mutant cbmc mutant.c \
      timeout -k 5 60 cbmc --unwind 2 --no-unwinding-assertions mutant.c
  done
}

fuzz_json_symtab() {
  local n=$1
  local -a seeds
  mapfile -t seeds < <(find "$basedir/regression" -name "*.json_symtab" | sort)
  if [ ${#seeds[@]} -eq 0 ] ; then
    echo "No JSON symbol tables found, skipping"
    return 0
  fi
  echo "Fuzzing the JSON symbol table reader with $n mutants of ${#seeds[@]} inputs"

  for ((i = 0; i < n; ++i)); do
    mutate "${seeds[$((RANDOM % ${#seeds[@]}))]}" mutant.json_symtab
    run_mutant symtab2gb mutant.json_symtab \
      timeout -k 5 60 symtab2gb mutant.json_symtab --out mutant.gb
  done
}

# Determine the number of mutants per surface; the default is 100.
N=$1
if [ -z "$N" ] ; then
  N=100
fi

# A seed may be given to repeat an earlier run; otherwise pick a fresh one.
seed=$2
if [ -z "$seed" ] ; then
  seed=$(od -A n -t u4 -N 4 /dev/urandom | tr -d " ")
fi
RANDOM=$seed
echo "Random seed being used: $seed"
echo "To repeat this run: scripts/fuzz.sh $N $seed"

cd "$workdir"
trap print_seed ERR

fuzz_c "$N"
fuzz_json_symtab "$N"

cd "$basedir"
rm -rf "$workdir"
echo "No crashes found"
