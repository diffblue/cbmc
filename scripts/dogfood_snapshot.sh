#!/usr/bin/env bash
# scripts/dogfood_snapshot.sh
#
# Run the dog-food sweep (scripts/dogfood_goto_cc.sh --expand) in the
# BACKGROUND against a frozen snapshot, so that ongoing development in
# the working tree cannot disturb it:
#
#   * the SOURCES being compiled come from a git worktree checked out at
#     a fixed commit (default: HEAD), not from the working tree;
#   * the -I paths are rewritten to point into that worktree, so edited
#     headers in the working tree are not picked up either;
#   * the goto-cc BINARY is copied into the snapshot directory, so a
#     rebuild of build-work/ mid-sweep does not change the compiler;
#   * the sweep runs detached (setsid + nohup), single-threaded, at the
#     lowest CPU/IO priority (nice 19 / ionice idle), so foreground
#     builds and regression runs are barely affected and the sweep is
#     not killed when the launching shell exits;
#   * every goto-cc invocation is bounded in time (TIMEOUT, default 900s
#     -- goto-symex translation units take ~5 minutes each) and in
#     memory (ulimit -v, default 12 GiB).
#
# Usage:
#   scripts/dogfood_snapshot.sh [--files LIST] [COMMIT] [GOTO_CC] [DIRS...]
#     --files LIST  sweep exactly the files listed (one repo-relative
#                   path per line) instead of DIRS -- e.g. the file set of
#                   an earlier sweep log, for a like-for-like --compare:
#                   grep -E '^(OK|OK_NOISY|FAIL|CRASH) ' OLD.log |
#                     awk '{print $2}' | sed 's/:$//' > LIST
#     COMMIT   git rev to snapshot (default HEAD)
#     GOTO_CC  goto-cc binary to freeze (default build-work/bin/goto-cc)
#     DIRS     directories (relative to the repo) to sweep; default is
#              the script's DOGFOOD_DIRS set
#
# Environment overrides: TIMEOUT (seconds per file), MEM_KIB (ulimit -v),
# SNAP_ROOT (where snapshots live, default /tmp/dogfood-snapshots).
#
# Output: <snapshot>/sweep.log (per-file OK/OK_NOISY/FAIL/CRASH lines and
# the summary), <snapshot>/DONE when finished (contains the exit code).
# Compare two sweeps with:
#   scripts/dogfood_snapshot.sh --compare OLD.log NEW.log
# Clean up a finished snapshot with:
#   git worktree remove --force <snapshot>/tree

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SNAP_ROOT="${SNAP_ROOT:-/tmp/dogfood-snapshots}"
TIMEOUT="${TIMEOUT:-900}"
MEM_KIB="${MEM_KIB:-12000000}"

if [ "${1:-}" = "--compare" ]; then
  old="$2"; new="$3"
  join -j1 \
    <(grep -E "^(OK|OK_NOISY|FAIL|CRASH) " "$old" | awk '{print $2, $1}' | sort) \
    <(grep -E "^(OK|OK_NOISY|FAIL|CRASH) " "$new" | awk '{print $2, $1}' | sort) \
    | awk '$2!=$3{printf "%-50s %-9s -> %s\n", $1, $2, $3}'
  echo "--- only in $new:"
  comm -13 <(grep -E "^(OK|OK_NOISY|FAIL|CRASH) " "$old" | awk '{print $2}' | sort) \
           <(grep -E "^(OK|OK_NOISY|FAIL|CRASH) " "$new" | awk '{print $2}' | sort)
  exit 0
fi

files_list=""
if [ "${1:-}" = "--files" ]; then
  files_list="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
  shift 2
fi

commit="$(git -C "$REPO_ROOT" rev-parse --short "${1:-HEAD}")"
goto_cc="${2:-$REPO_ROOT/build-work/bin/goto-cc}"
shift $(( $# >= 2 ? 2 : $# )) || true
dirs="${*:-}"

snap="$SNAP_ROOT/$commit-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$snap"

# 1. frozen sources
git -C "$REPO_ROOT" worktree add --detach "$snap/tree" "$commit" >/dev/null

# 2. frozen compiler
cp "$goto_cc" "$snap/goto-cc"

# 3. include paths rewritten into the snapshot (compile_commands.json is
#    only read for its -I flags)
src_cc="${COMPILE_COMMANDS:-$REPO_ROOT/build-work/compile_commands.json}"
sed "s|$REPO_ROOT|$snap/tree|g" "$src_cc" > "$snap/compile_commands.json"

# 4. detached, low-priority, bounded sweep
cat > "$snap/run.sh" <<EOF
#!/usr/bin/env bash
cd "$snap/tree"
ulimit -v $MEM_KIB
export GOTO_CC="$snap/goto-cc"
export COMPILE_COMMANDS="$snap/compile_commands.json"
export TIMEOUT="$TIMEOUT"
${dirs:+export DOGFOOD_DIRS="$dirs"}
${files_list:+export DOGFOOD_FILES="$files_list"}
echo "snapshot: $commit  goto-cc: $goto_cc  started: \$(date -u +%FT%TZ)"
nice -n 19 ionice -c 3 scripts/dogfood_goto_cc.sh --expand
rc=\$?
echo "finished: \$(date -u +%FT%TZ) rc=\$rc"
echo "\$rc" > "$snap/DONE"
EOF
chmod +x "$snap/run.sh"
setsid nohup "$snap/run.sh" > "$snap/sweep.log" 2>&1 < /dev/null &
echo "$!" > "$snap/PID"

echo "snapshot: $snap"
echo "log:      $snap/sweep.log"
echo "pid:      $(cat "$snap/PID")"
echo "progress: grep -cE '^(OK|OK_NOISY|FAIL|CRASH) ' $snap/sweep.log ; done when $snap/DONE exists"
