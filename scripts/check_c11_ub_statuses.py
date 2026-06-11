#!/usr/bin/env python3
"""Sanity-check the C11 undefined-behavior table.

Every row's "Checked?" cell must be one of the expected status values. Two
status-cell typos ('mo', and an empty cell) previously went unnoticed in this
table; this guards against that class of regression.
"""
import sys

PATH = "doc/cprover-manual/c11-undefined-behavior.md"
VALID = {"yes", "no", "partial", "partially"}

errors = []
with open(PATH) as f:
    for n, line in enumerate(f, 1):
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) != 2:  # not a row of the two-column table
            continue
        status = cells[1]
        if status in ("Checked?", "---"):  # header / separator row
            continue
        if status not in VALID:
            errors.append((n, status))

if errors:
    print(f"{PATH}: invalid status cell(s); expected one of {sorted(VALID)}:")
    for n, status in errors:
        print(f"  line {n}: {status!r}")
    sys.exit(1)

print(f"{PATH}: all status cells valid")
