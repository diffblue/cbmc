#!/usr/bin/env bash
#
# Verify that src/ansi-c/library/x86_intrinsics.c is in sync with its
# generator (scripts/generate_intrinsic_models.py). The generated library
# must never be hand-edited; this check fails if regenerating it would
# produce a different file, so a stale committed copy (or a MODELS change
# without regeneration) is caught in CI.

set -e

script_dir=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$script_dir/.." && pwd)
committed="$root/src/ansi-c/library/x86_intrinsics.c"

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

python3 "$script_dir/generate_intrinsic_models.py" --cbmc-root "$root" -o "$tmp"

if ! diff -u "$committed" "$tmp"; then
  echo
  echo "ERROR: src/ansi-c/library/x86_intrinsics.c is out of sync with"
  echo "scripts/generate_intrinsic_models.py. Regenerate it with:"
  echo "  python3 scripts/generate_intrinsic_models.py \\"
  echo "    -o src/ansi-c/library/x86_intrinsics.c"
  exit 1
fi

echo "x86_intrinsics.c is in sync with the generator."
