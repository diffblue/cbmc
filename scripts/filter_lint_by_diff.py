#!/usr/bin/env python

import sys
import unidiff
import os.path

if len(sys.argv) != 3:
  print >>sys.stderr, "Usage: filter_lint_by_diff.py diff.patch repository_root_directory < cpplint_warnings.txt"
  sys.exit(1)

repository_root = sys.argv[2]

# Create a set of all the files and the specific lines within that file that are in the diff
added_lines = set()
for diff_file in unidiff.PatchSet.from_filename(sys.argv[1]):
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

# Print the lines that are in the set
for line in sys.stdin:
  line_parts = line.split(":")
  if len(line_parts) < 3:
    continue
  filename = os.path.join(repository_root, line_parts[0])
  linenum = int(line_parts[1])
  if (filename, linenum) in added_lines:
    sys.stdout.write(line)
