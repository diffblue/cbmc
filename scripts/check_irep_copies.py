#!/usr/bin/env python3
"""Detect irept copy-then-modify patterns that could use std::move.

Scans C++ source files for patterns like:
  exprt x = some_expr;   // copy
  x.set(...);            // modify

Where some_expr is a local variable or function return that isn't used
after the copy, meaning std::move could avoid the copy.

This is a heuristic grep-based checker, not a full AST analysis.
It flags candidates for manual review, not guaranteed fixes.

Usage:
  python3 scripts/check_irep_copies.py src/goto-symex/*.cpp
"""

import re
import sys
from pathlib import Path

# Types that inherit from irept (copy = refcount increment + potential detach)
IREP_TYPES = {
    "exprt", "typet", "codet", "irept",
    "symbol_exprt", "ssa_exprt", "member_exprt", "index_exprt",
    "if_exprt", "typecast_exprt", "address_of_exprt",
    "equal_exprt", "notequal_exprt", "and_exprt", "or_exprt",
    "not_exprt", "implies_exprt", "plus_exprt", "minus_exprt",
    "mult_exprt", "div_exprt", "mod_exprt",
    "binary_exprt", "unary_exprt", "multi_ary_exprt",
    "dereference_exprt", "byte_extract_exprt",
    "struct_exprt", "array_exprt", "union_exprt",
    "constant_exprt", "string_constantt",
    "source_locationt", "code_assignt", "code_returnt",
    "goto_programt::instructiont",
    "array_typet", "pointer_typet", "struct_typet",
    "signedbv_typet", "unsignedbv_typet", "floatbv_typet",
}

# Methods that modify an irept (trigger write()/detach())
MODIFY_METHODS = {
    "set", "add", "remove", "clear", "swap",
    "set_identifier", "set_expression", "set_level_0",
    "set_level_1", "set_level_2", "remove_level_2",
    "operands", "type", "op0", "op1", "op2", "op3",
    "make_typecast", "make_not",
}

# Patterns that indicate the source is NOT used after the copy
# (conservative: only flag when source is a simple local variable)


def check_file(filepath):
    """Check a single file for copy-then-modify patterns."""
    findings = []
    lines = Path(filepath).read_text().splitlines()

    for i, line in enumerate(lines):
        # Match: Type varname = source;
        # where Type is an irep type and source is not std::move(...)
        m = re.match(
            r'\s+(\w+)\s+(\w+)\s*=\s*(.+?)\s*;',
            line
        )
        if not m:
            continue

        typename, varname, source = m.groups()

        # Skip if not an irep type
        if typename not in IREP_TYPES:
            continue

        # Skip if already using std::move
        if "std::move" in source or "move(" in source:
            continue

        # Skip const
        if re.match(r'\s*const\s', line):
            continue

        # Check if the variable is modified in the next few lines
        modified = False
        source_reused = False
        # Extract the source variable name (if it's a simple variable)
        source_var = re.match(r'(\w+)', source.strip())
        source_var = source_var.group(1) if source_var else None

        for j in range(i + 1, min(i + 15, len(lines))):
            next_line = lines[j]
            # Check if varname is modified
            if re.search(
                rf'\b{varname}\b\s*\.\s*('
                + '|'.join(MODIFY_METHODS) + r')\s*\(',
                next_line
            ):
                modified = True
            # Check if varname is passed to to_*_expr() which returns
            # a mutable reference
            if re.search(rf'to_\w+_expr\s*\(\s*{varname}\s*\)', next_line):
                modified = True
            # Check if source variable is used after the copy
            if source_var and re.search(
                rf'\b{source_var}\b', next_line
            ):
                source_reused = True

        if modified and not source_reused and source_var:
            findings.append((i + 1, varname, typename, source.strip()))

    return findings


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <file.cpp> [file2.cpp ...]")
        sys.exit(1)

    total = 0
    for filepath in sys.argv[1:]:
        findings = check_file(filepath)
        for lineno, var, typ, src in findings:
            print(f"{filepath}:{lineno}: {typ} {var} = {src}  "
                  f"[could use std::move({src})]")
            total += 1

    if total:
        print(f"\n{total} potential unnecessary copies found.")
    else:
        print("No unnecessary copies found.")


if __name__ == "__main__":
    main()
