#!/usr/bin/env bash
# test.pl driver for the F.16 pass-by-value checker regression corpus.
#
# Usage (via test.pl): chain.sh <checker> [--fix] <fixture.cpp>
#
# The fixtures are self-contained (they declare their own stub `dstringt` /
# `irep_idt`), so the checker is run with a bare `-- -std=c++17` rather than a
# compile_commands.json.  Without `--fix` the checker's findings are printed;
# with `--fix` the rewritten fixture is printed (on a copy) so the expected
# post-rewrite text can be matched.
#
# The checker must already be built; scripts/run_pass_by_value_check.sh builds
# it, and the CI job runs that before this corpus.

set -e

checker="$1"
shift

if [ ! -x "$checker" ]; then
  echo "Error: checker '$checker' not built." >&2
  echo "Run scripts/run_pass_by_value_check.sh first to build it." >&2
  exit 1
fi

# The fixture is the last argument; anything before it is options.
fixture="${@: -1}"
set -- "${@:1:$#-1}"

if [ "${1:-}" = "--fix" ]; then
  work="$(mktemp --suffix=.cpp)"
  trap 'rm -f "$work"' EXIT
  cp "$fixture" "$work"
  "$checker" --fix "$work" -- -std=c++17 >/dev/null 2>&1 || true
  cat "$work"
else
  "$checker" "$fixture" -- -std=c++17
fi
