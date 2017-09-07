#!/usr/bin/env python

from __future__ import print_function

def filter_by_lines(diffed_file, added_lines_file, repository_root, in_stream, out_stream):

  import os.path
  import json

  diffed_file = sys.argv[1]
  added_lines_file = sys.argv[2]
  repository_root = sys.argv[3]

  # Get a set of all the files and the specific lines within that file to keep:
  with open(added_lines_file, "r") as f:
    added_lines = json.load(f)

  # added_lines is a dict filename -> line_number list
  # Make those into line_number sets instead:

  for k in added_lines:
    added_lines[k] = set(added_lines[k])

  # Print the lines that are in the set
  found = False
  for line in in_stream:
    line_parts = line.split(":")
    if len(line_parts) < 3:
      if found:
        # Print lines between a matching warning and the next warning
        out_stream.write(line)
      continue
    try:
      linenum = int(line_parts[1])
      found = False
      filename = line_parts[0]
      if not repository_root in filename:
        filename = os.path.join(repository_root, line_parts[0])
      if filename in added_lines and linenum in added_lines[filename]:
        found = True
        out_stream.write(line)
    except ValueError:
      if found:
        out_stream.write(line)
      continue

if __name__ == "__main__":

  import sys

  if len(sys.argv) != 4:
    print("filter_by_lines.py: filters lines of the form filename:line_number:message, retaining those matching a particular filename and list of line numbers", file=sys.stderr)
    print("Usage: filter_by_lines.py diffed_file added_lines.json repository_root_directory < warnings.txt", file=sys.stderr)
    sys.exit(1)

  filter_by_lines(sys.argv[1], sys.argv[2], sys.argv[3], sys.stdin, sys.stdout)
