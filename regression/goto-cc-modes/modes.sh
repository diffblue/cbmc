#!/bin/bash
# Test script for goto-cc mode-specific tests.
# Usage: modes.sh <goto-cc-binary> <mode-name> [args...]
#
# test.pl invokes: CMD OPTIONS 'INPUT'
# So this receives: modes.sh <goto-cc> <mode> [mode-args...] <input-file>
#
# Creates a symlink with the mode name and runs it with the remaining args.

GOTO_CC=$1
shift

MODE=$1
shift

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

ln -sf "$(realpath "$GOTO_CC")" "$TMPDIR/$MODE"
"$TMPDIR/$MODE" "$@"
