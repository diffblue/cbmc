#!/usr/bin/env python

from __future__ import print_function

def diff_to_added_lines(diff_file, repository_root, out_stream):

  try:
    import unidiff
  except ImportError:
    print("diff_to_added_lines.py requires unidiff, use `pip install --user unidiff` to install")
    sys.exit(1)

  import os.path
  import json

  # Create a set of all the files and the specific lines within that file that are in the diff
  added_lines = dict()

  for file_in_diff in unidiff.PatchSet.from_filename(diff_file):
    filename = file_in_diff.target_file
    # Skip files deleted in the tip (b side of the diff):
    if filename == "/dev/null":
      continue
    assert filename.startswith("b/")
    filename = os.path.join(repository_root, filename[2:])
    if filename not in added_lines:
      added_lines[filename] = []
    added_lines[filename].append(0)
    for diff_hunk in file_in_diff:
      for diff_line in diff_hunk:
        if diff_line.line_type == "+":
          if filename not in added_lines:
            added_lines[filename] = []
          added_lines[filename].append(diff_line.target_line_no)

  json.dump(added_lines, out_stream)

if __name__ == "__main__":

  import sys

  if len(sys.argv) != 3:
    print("diff_to_added_lines.py: converts a unified-diff file into a JSON dictionary mapping filenames onto an array of added or modified line numbers", file=sys.stderr)
    print("Usage: diff_to_added_lines.py diff.patch repository_root_directory", file=sys.stderr)

    sys.exit(1)

  diff_to_added_lines(sys.argv[1], sys.argv[2], sys.stdout)

diff_file = sys.argv[1]
repository_root = sys.argv[2]
