#!/bin/bash
# Check that man pages document values consistent with the implementation.
# This script is intended to be run as part of CI.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

errors=0

error() {
  echo "ERROR: $*" >&2
  errors=$((errors + 1))
}

# --- Exit codes ---
# Extract exit code definitions from src/util/exit_codes.h and verify
# that man pages document them correctly.

EXIT_CODES_H="$REPO_ROOT/src/util/exit_codes.h"

get_exit_code() {
  local name="$1"
  grep "#define $name" "$EXIT_CODES_H" | awk '{print $3}'
}

SAFE=$(get_exit_code CPROVER_EXIT_VERIFICATION_SAFE)
UNSAFE=$(get_exit_code CPROVER_EXIT_VERIFICATION_UNSAFE)
EXCEPTION=$(get_exit_code CPROVER_EXIT_EXCEPTION)

for manpage in cbmc jbmc; do
  MANFILE="$REPO_ROOT/doc/man/${manpage}.1"
  if [ ! -f "$MANFILE" ]; then
    error "$manpage.1: file not found"
    continue
  fi

  if ! grep -q "EXIT STATUS" "$MANFILE"; then
    error "$manpage.1: missing EXIT STATUS section"
    continue
  fi

  # Check that the documented exit codes match the implementation
  if ! grep -q "^\.B $SAFE\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code $SAFE (VERIFICATION_SAFE)"
  fi
  if ! grep -q "^\.B $UNSAFE\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code $UNSAFE (VERIFICATION_UNSAFE)"
  fi
  if ! grep -q "^\.B $EXCEPTION\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code $EXCEPTION (EXCEPTION/INTERNAL_ERROR)"
  fi
done

# --- Default object bits ---
# Extract default_object_bits from src/util/config.h and verify man pages.

CONFIG_H="$REPO_ROOT/src/util/config.h"

# C/C++ default (from ansi_c struct)
C_DEFAULT=$(sed -n '/struct ansi_ct/,/^  } ansi_c;/p' "$CONFIG_H" | \
  grep 'default_object_bits' | head -1 | grep -o '[0-9]\+')
# Java default
JAVA_DEFAULT=$(sed -n '/struct javat/,/^  } java;/p' "$CONFIG_H" | \
  grep 'default_object_bits' | head -1 | grep -o '[0-9]\+')

CBMC_MAN="$REPO_ROOT/doc/man/cbmc.1"
JBMC_MAN="$REPO_ROOT/doc/man/jbmc.1"

if [ -n "$C_DEFAULT" ]; then
  if ! grep -q "default is $C_DEFAULT" "$CBMC_MAN"; then
    error "cbmc.1: --object-bits default ($C_DEFAULT) not documented or mismatched"
  fi
else
  error "Could not extract C/C++ default_object_bits from config.h"
fi

if [ -n "$JAVA_DEFAULT" ]; then
  if ! grep -q "default is $JAVA_DEFAULT" "$JBMC_MAN"; then
    error "jbmc.1: --object-bits default ($JAVA_DEFAULT) not documented or mismatched"
  fi
else
  error "Could not extract Java default_object_bits from config.h"
fi

# --- Default max field sensitivity array size ---

MAGIC_H="$REPO_ROOT/src/util/magic.h"
FIELD_SENS_DEFAULT=$(grep 'DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE' "$MAGIC_H" | \
  grep -o '[0-9]\+')

if [ -n "$FIELD_SENS_DEFAULT" ]; then
  for manpage in cbmc jbmc; do
    MANFILE="$REPO_ROOT/doc/man/${manpage}.1"
    if grep -q 'field.sensitivity.array.size' "$MANFILE"; then
      if ! grep -q "default is $FIELD_SENS_DEFAULT" "$MANFILE"; then
        error "$manpage.1: --max-field-sensitivity-array-size default ($FIELD_SENS_DEFAULT) not documented or mismatched"
      fi
    fi
  done
else
  error "Could not extract DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE from magic.h"
fi

# --- Summary ---
if [ "$errors" -gt 0 ]; then
  echo "FAILED: $errors error(s) found in man page consistency checks" >&2
  exit 1
else
  echo "PASSED: all man page consistency checks passed"
  exit 0
fi
