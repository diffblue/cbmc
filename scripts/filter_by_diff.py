#!/usr/bin/env python

import sys
import unidiff
import os.path

if len(sys.argv) != 4:
  print >>sys.stderr, "Usage: filter_by_diff.py diffed_file diff.patch repository_root_directory < warnings.txt"
  sys.exit(1)

diffed_file = sys.argv[1]
diff_file = sys.argv[2]
repository_root = sys.argv[3]

# Create a set of all the files and the specific lines within that file that are in the diff
added_lines = set()
for diff_file in unidiff.PatchSet.from_filename(diff_file):
  filename = diff_file.target_file
  # Skip files deleted in the tip (b side of the diff):
  if filename == "/dev/null":
    continue
  assert filename.startswith("b/")
  filename = os.path.join(repository_root, filename[2:])
  if filename != diffed_file:
    continue
  added_lines.add((filename, 0))
  for diff_hunk in diff_file:
    for diff_line in diff_hunk:
      if diff_line.line_type == "+":
        added_lines.add((filename, diff_line.target_line_no))

# Print the lines that are in the set
found = False
for line in sys.stdin:
  line_parts = line.split(":")
  if len(line_parts) < 3:
    if found:
      # Print lines between a matching warning and the next warning
      sys.stdout.write(line)
    continue
  try:
    linenum = int(line_parts[1])
    found = False
    filename = line_parts[0]
    if not repository_root in filename:
      filename = os.path.join(repository_root, line_parts[0])
    if (filename, linenum) in added_lines:
      found = True
      sys.stdout.write(line)
  except ValueError:
    if found:
      sys.stdout.write(line)
    continue
