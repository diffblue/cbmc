#!/bin/bash
# Check that man pages document values consistent with the implementation.
# This script is intended to be run as part of CI.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MAN_DIR="$REPO_ROOT/doc/man"

errors=0

error() {
  echo "ERROR: $*" >&2
  errors=$((errors + 1))
}

# --- Version consistency ---
# All man pages must reference the same version as src/config.inc.

CBMC_VERSION=$(grep '^CBMC_VERSION' "$REPO_ROOT/src/config.inc" | \
  sed 's/.*= *//')

if [ -z "$CBMC_VERSION" ]; then
  error "Could not extract CBMC_VERSION from src/config.inc"
else
  for manfile in "$MAN_DIR"/*.1; do
    name=$(basename "$manfile" .1)
    # Extract version from .TH source string, e.g. "cbmc-6.8.0"
    th_version=$(head -1 "$manfile" | grep -oP '\d+\.\d+\.\d+' || true)
    if [ -z "$th_version" ]; then
      error "$name.1: no version found in .TH header"
    elif [ "$th_version" != "$CBMC_VERSION" ]; then
      error "$name.1: .TH version ($th_version) does not match" \
        "CBMC_VERSION ($CBMC_VERSION)"
    fi
  done
fi

# --- Date consistency ---
# All man pages should have the same date, and it must be parseable by
# mandoc (i.e. "Month Day, Year" format).

dates=()
for manfile in "$MAN_DIR"/*.1; do
  name=$(basename "$manfile" .1)
  # Extract the date field (third argument to .TH)
  th_date=$(head -1 "$manfile" | sed 's/.*"1" "//;s/".*//')
  if [ -z "$th_date" ]; then
    error "$name.1: no date found in .TH header"
    continue
  fi
  # Verify the date contains a day number (mandoc requirement)
  if ! echo "$th_date" | grep -qP '^\w+ \d+, \d{4}$'; then
    error "$name.1: .TH date \"$th_date\" is not in" \
      "\"Month Day, Year\" format required by mandoc"
  fi
  dates+=("$th_date")
done

# Check all dates are the same
if [ ${#dates[@]} -gt 0 ]; then
  first="${dates[0]}"
  for d in "${dates[@]}"; do
    if [ "$d" != "$first" ]; then
      error "Man page dates are inconsistent (found both" \
        "\"$first\" and \"$d\")"
      break
    fi
  done
fi

# --- .TH name matches filename ---
# The name in .TH must be the uppercase version of the filename.

for manfile in "$MAN_DIR"/*.1; do
  name=$(basename "$manfile" .1)
  expected=$(echo "$name" | tr '[:lower:]' '[:upper:]')
  th_name=$(head -1 "$manfile" | awk '{print $2}')
  if [ "$th_name" != "$expected" ]; then
    error "$name.1: .TH name ($th_name) does not match expected ($expected)"
  fi
done

# --- Required sections ---
# Every man page must have at least NAME, SYNOPSIS, DESCRIPTION, and BUGS.

for manfile in "$MAN_DIR"/*.1; do
  name=$(basename "$manfile" .1)
  for section in NAME SYNOPSIS DESCRIPTION BUGS; do
    if ! grep -q "^\.SH.*$section" "$manfile"; then
      error "$name.1: missing required section $section"
    fi
  done
done

# --- NAME section format ---
# The NAME section must follow "toolname \- short description" format
# for whatis(1)/apropos(1) compatibility.

for manfile in "$MAN_DIR"/*.1; do
  name=$(basename "$manfile" .1)
  name_line=$(awk '/^\.SH NAME/{getline; print; exit}' "$manfile")
  # Must contain " \- " separator (roff NAME convention)
  if ! echo "$name_line" | grep -q ' \\- '; then
    error "$name.1: NAME line does not use \"\\-\" separator:" \
      "\"$name_line\""
  fi
  # The tool name (with \- unescaped) should match the filename
  tool_in_name=$(echo "$name_line" | sed 's/ \\-.*//' | sed 's/\\-/-/g')
  if [ "$tool_in_name" != "$name" ]; then
    error "$name.1: tool name in NAME section ($tool_in_name)" \
      "does not match filename ($name)"
  fi
done

# --- SEE ALSO cross-references ---
# Every man page referenced in SEE ALSO with section (1) should have a
# corresponding .1 file in doc/man/.

for manfile in "$MAN_DIR"/*.1; do
  name=$(basename "$manfile" .1)
  # Extract tool names from SEE ALSO that reference section 1
  refs=$(awk '/^\.SH.*SEE ALSO/{found=1; next} found && /^\.SH/{exit} found' \
    "$manfile" | grep -oP '[\w\\-]+ \(1\)' | sed 's/\\-/-/g;s/ (1)//' || true)
  for ref in $refs; do
    # Only check our own tools (skip system commands like gcc, as, ld, gdb)
    if [ -f "$MAN_DIR/$ref.1" ] || echo "$ref" | grep -qP '^(goto-|cbmc|jbmc|jdiff|janalyzer|crangler|symtab2gb|memory-analyzer|goto-synthesizer)'; then
      if [ ! -f "$MAN_DIR/$ref.1" ]; then
        error "$name.1: SEE ALSO references $ref(1) but" \
          "doc/man/$ref.1 does not exist"
      fi
    fi
  done
done

# --- Exit codes ---
# Extract exit code definitions from src/util/exit_codes.h and verify
# that man pages document them correctly.

EXIT_CODES_H="$REPO_ROOT/src/util/exit_codes.h"

get_exit_code() {
  local name="$1"
  grep "#define $name" "$EXIT_CODES_H" | awk '{print $3}' || true
}

SAFE=$(get_exit_code CPROVER_EXIT_VERIFICATION_SAFE)
UNSAFE=$(get_exit_code CPROVER_EXIT_VERIFICATION_UNSAFE)
EXCEPTION=$(get_exit_code CPROVER_EXIT_EXCEPTION)
USAGE=$(get_exit_code CPROVER_EXIT_USAGE_ERROR)
PARSE=$(get_exit_code CPROVER_EXIT_PARSE_ERROR)

if [ -z "$SAFE" ] || [ -z "$UNSAFE" ] || [ -z "$EXCEPTION" ] ||
   [ -z "$USAGE" ] || [ -z "$PARSE" ]; then
  error "Could not extract one or more exit codes from $EXIT_CODES_H"
else
  for manpage in cbmc jbmc; do
  MANFILE="$MAN_DIR/${manpage}.1"
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
    error "$manpage.1: EXIT STATUS does not document exit code" \
      "$SAFE (VERIFICATION_SAFE)"
  fi
  if ! grep -q "^\.B $UNSAFE\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code" \
      "$UNSAFE (VERIFICATION_UNSAFE)"
  fi
  if ! grep -q "^\.B $USAGE\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code" \
      "$USAGE (USAGE_ERROR)"
  fi
  if ! grep -q "^\.B $PARSE\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code" \
      "$PARSE (PARSE_ERROR)"
  fi
  if ! grep -q "^\.B $EXCEPTION\$" "$MANFILE"; then
    error "$manpage.1: EXIT STATUS does not document exit code" \
      "$EXCEPTION (EXCEPTION/INTERNAL_ERROR)"
  else
    # Presence alone is not enough: exit code 6 covers internal errors and
    # unhandled exceptions (not parse/usage errors), so check the description
    # text too. This guards against mis-attributing 6 to parse/option errors.
    desc=$(grep -A1 "^\.B $EXCEPTION\$" "$MANFILE" | tail -1)
    if ! printf '%s' "$desc" | grep -qiE 'internal|exception'; then
      error "$manpage.1: EXIT STATUS description for exit code $EXCEPTION" \
        "should mention an internal error or exception, but reads: $desc"
    fi
  fi
done
fi

# --- Default object bits ---
# Extract default_object_bits from src/util/config.h and verify man pages.

CONFIG_H="$REPO_ROOT/src/util/config.h"

# C/C++ default (from ansi_c struct)
C_DEFAULT=$(sed -n '/struct ansi_ct/,/^  } ansi_c;/p' "$CONFIG_H" | \
  grep 'default_object_bits' | head -1 | grep -o '[0-9]\+') || true
# Java default
JAVA_DEFAULT=$(sed -n '/struct javat/,/^  } java;/p' "$CONFIG_H" | \
  grep 'default_object_bits' | head -1 | grep -o '[0-9]\+') || true

CBMC_MAN="$MAN_DIR/cbmc.1"
JBMC_MAN="$MAN_DIR/jbmc.1"

if [ -n "$C_DEFAULT" ]; then
  if ! grep -q "default is $C_DEFAULT" "$CBMC_MAN"; then
    error "cbmc.1: --object-bits default ($C_DEFAULT)" \
      "not documented or mismatched"
  fi
else
  error "Could not extract C/C++ default_object_bits from config.h"
fi

if [ -n "$JAVA_DEFAULT" ]; then
  if ! grep -q "default is $JAVA_DEFAULT" "$JBMC_MAN"; then
    error "jbmc.1: --object-bits default ($JAVA_DEFAULT)" \
      "not documented or mismatched"
  fi
else
  error "Could not extract Java default_object_bits from config.h"
fi

# --- Default max field sensitivity array size ---

MAGIC_H="$REPO_ROOT/src/util/magic.h"
FIELD_SENS_DEFAULT=$(grep 'DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE' \
  "$MAGIC_H" | grep -o '[0-9]\+') || true

if [ -n "$FIELD_SENS_DEFAULT" ]; then
  for manpage in cbmc jbmc; do
    MANFILE="$MAN_DIR/${manpage}.1"
    if grep -q 'field.*sensitivity.*array.*size' "$MANFILE"; then
      if ! grep -q "default is $FIELD_SENS_DEFAULT" "$MANFILE"; then
        error "$manpage.1: --max-field-sensitivity-array-size default" \
          "($FIELD_SENS_DEFAULT) not documented or mismatched"
      fi
    fi
  done
else
  error "Could not extract DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE" \
    "from magic.h"
fi

# --- Man page coverage ---
# Every tool that is installed (install(TARGETS ...)) should have a man page.
#
# We derive the tool name from the install(TARGETS <name> ...) argument rather
# than the first add_executable(), as the latter may be a helper target.
# Residual assumption: the installed target name matches the man-page basename
# (doc/man/<target>.1). Targets that rename their binary via OUTPUT_NAME or
# set_target_properties are not handled; add an explicit mapping here should
# such a case arise.

for cmakefile in "$REPO_ROOT"/src/*/CMakeLists.txt \
                 "$REPO_ROOT"/jbmc/src/*/CMakeLists.txt; do
  [ -f "$cmakefile" ] || continue
  # Only consider directories that install an executable
  grep -q 'install(TARGETS' "$cmakefile" || continue
  tool=$(grep -oE 'install\(TARGETS[[:space:]]+[A-Za-z0-9_.-]+' "$cmakefile" \
    | head -1 | awk '{print $NF}') || true
  [ -z "$tool" ] && continue
  # Only check executables: skip installed libraries (add_library targets).
  grep -qE "add_executable\(${tool}[[:space:]]" "$cmakefile" || continue
  if [ ! -f "$MAN_DIR/$tool.1" ]; then
    error "$tool: installed executable has no man page" \
      "at doc/man/$tool.1"
  fi
done

# --- Summary ---
if [ "$errors" -gt 0 ]; then
  echo "FAILED: $errors error(s) found in man page consistency checks" >&2
  exit 1
else
  echo "PASSED: all man page consistency checks passed"
  exit 0
fi
