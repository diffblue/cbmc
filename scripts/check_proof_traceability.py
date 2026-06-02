#!/usr/bin/env python3
"""Proof-traceability coverage check for the algebraic pre-solver.

Closes the gap that allowed the Item 13/14 soundness bugs to ship
despite a Lean soundness development: the previous bi-directional
audit only verified that *annotated* steps had proofs, so an
*unannotated* soundness-critical step (the Rabinowitsch disequality
encoding) was invisible to it.

This script enforces two invariants and exits non-zero on violation:

1. RESOLUTION: every `// PROOF: formal-proofs/<File>.lean::<thm>`
   reference in the C++ sources resolves to a real declaration
   (theorem/lemma/def) of that name in the referenced Lean file.

2. COVERAGE: every UNSAT-concluding site
   (`prop.l_set_to_true(const_literal(false))`) inside
   `boolbvt::try_algebraic_solve` carries a `// PROOF:` annotation
   within the preceding window of lines. An UNSAT conclusion is the
   soundness-critical step; it must be justified.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
LEAN_DIR = ROOT / "formal-proofs"
BOOLBV = SRC / "solvers" / "flattening" / "boolbv.cpp"
COVERAGE_WINDOW = 40  # lines a PROOF annotation may precede an UNSAT site

# Reference like: formal-proofs/File.lean::Maybe::Namespaced::thm_name
# The thm name may continue onto the next `//` comment line.
# Lean declaration names may end with a prime ('), e.g. foo_unsat'.
REF_RE = re.compile(r"formal-proofs/(\w+)\.lean::([\w:']*)")


def lean_decl_names(path: Path) -> set:
    """All declared theorem/lemma/def names in a Lean file."""
    names = set()
    decl = re.compile(r"^\s*(?:theorem|lemma|def|noncomputable def)\s+([\w']+)")
    for line in path.read_text().splitlines():
        m = decl.match(line)
        if m:
            names.add(m.group(1))
    return names


def collect_proof_refs(text: str):
    """Yield (lean_file, thm_name) for each PROOF reference.

    Handles the case where `File.lean::` ends a comment line and the
    theorem name is on the following `//` continuation line.
    """
    lines = text.splitlines()
    for i, line in enumerate(lines):
        for m in REF_RE.finditer(line):
            lean_file, thm = m.group(1), m.group(2)
            if not thm:
                # name continues on the next comment line
                if i + 1 < len(lines):
                    nxt = lines[i + 1]
                    cm = re.search(r"//\s*([\w:']+)", nxt)
                    if cm:
                        thm = cm.group(1)
            if thm:
                # last `::` component is the actual declaration name
                yield lean_file, thm.split("::")[-1]


def find_function_span(text: str, signature: str):
    """Return (start_line, end_line) 0-indexed for a brace-balanced
    function body following `signature`."""
    lines = text.splitlines()
    start = next(
        (i for i, ln in enumerate(lines) if signature in ln), None)
    if start is None:
        return None
    depth = 0
    seen = False
    for i in range(start, len(lines)):
        depth += lines[i].count("{") - lines[i].count("}")
        if "{" in lines[i]:
            seen = True
        if seen and depth <= 0:
            return start, i
    return start, len(lines) - 1


def main() -> int:
    errors = []

    # ---- Invariant 1: resolution ----
    lean_cache = {}
    for cpp in SRC.rglob("*.cpp"):
        text = cpp.read_text(errors="ignore")
        for lean_file, thm in collect_proof_refs(text):
            lpath = LEAN_DIR / f"{lean_file}.lean"
            if not lpath.exists():
                errors.append(
                    f"{cpp.relative_to(ROOT)}: PROOF references missing "
                    f"file formal-proofs/{lean_file}.lean")
                continue
            names = lean_cache.setdefault(lpath, lean_decl_names(lpath))
            if thm not in names:
                errors.append(
                    f"{cpp.relative_to(ROOT)}: PROOF references "
                    f"{lean_file}.lean::{thm} but no such declaration "
                    f"exists in that file")

    # ---- Invariant 2: coverage of UNSAT sites in try_algebraic_solve ----
    text = BOOLBV.read_text()
    lines = text.splitlines()
    span = find_function_span(text, "bool boolbvt::try_algebraic_solve()")
    if span is None:
        errors.append("could not locate try_algebraic_solve in boolbv.cpp")
    else:
        lo, hi = span
        for i in range(lo, hi + 1):
            if "l_set_to_true(const_literal(false))" in lines[i]:
                window = "\n".join(lines[max(lo, i - COVERAGE_WINDOW):i])
                if "PROOF:" not in window:
                    errors.append(
                        f"boolbv.cpp:{i + 1}: UNSAT conclusion without a "
                        f"// PROOF: annotation within {COVERAGE_WINDOW} "
                        f"preceding lines (soundness-critical step must "
                        f"be justified)")

    if errors:
        print("Proof-traceability check FAILED:\n")
        for e in errors:
            print(f"  - {e}")
        return 1
    print("Proof-traceability check passed: all PROOF references resolve "
          "and every UNSAT conclusion in try_algebraic_solve is annotated.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
