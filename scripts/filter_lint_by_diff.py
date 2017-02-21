#!/usr/bin/env python

import sys
import unidiff
import os.path

if len(sys.argv) != 3:
  print >>sys.stderr, "Usage: filter_lint_by_diff.py diff.patch repository_root_directory < cpplint_warnings.txt"
  sys.exit(1)

added_lines = set()
repository_root = sys.argv[2]

with open(sys.argv[1], "r") as f:
  diff = unidiff.PatchSet(f)
  for diff_file in diff:
    filename = diff_file.target_file
    # Skip files deleted in the tip (b side of the diff):
    if filename == "/dev/null":
      continue
    assert filename.startswith("b/")
    filename = os.path.join(repository_root, filename[2:])
    added_lines.add((filename, 0))
    for diff_hunk in diff_file:
      for diff_line in diff_hunk:
        if diff_line.line_type == "+":
          added_lines.add((filename, diff_line.target_line_no))

for l in sys.stdin:
  bits = l.split(":")
  if len(bits) < 3:
    continue
  filename = os.path.join(repository_root, bits[0])
  linenum = int(bits[1])
  if (filename, linenum) in added_lines:
    sys.stdout.write(l)
