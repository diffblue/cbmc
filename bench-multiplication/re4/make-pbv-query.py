#!/usr/bin/env python3
"""Generate the partial-bit-vector identity benchmarks for the Re 4
paper subsection. Each query is universal-equational and UNSAT.

Categories:
  bvxor-cancel:  (a XOR b) XOR b = a
  demorgan:      ~(a & b) = ~a | ~b
  bvnot-involution: ~~a = a
  bvand-zero:    a & 0 = 0
  bvor-self:     a | a = a
  bvxor-self:    a XOR a = 0
  bvand-idem:    a & a = a
  shift-identity: (2x) >> 1 = x given x < 2^{d-1}
  compound-shift: ((a+b)>>1) = ((b+a)>>1)
  toom-scaled:   ((a+b)-(a-b))>>1 = b given b < 2^{d-1}
  toom-distrib:  ((a+b)+(c+d))>>2 = ((a+c)+(b+d))>>2
"""

import argparse
import sys


def emit(query, bw):
    """Emit an SMT-LIB query."""
    print(f"; Partial bit-vector identity: {query['name']} at {bw}-bit")
    print(f"; Expected: UNSAT")
    print(f"(set-logic QF_BV)")
    for v in query["vars"]:
        print(f"(declare-const {v} (_ BitVec {bw}))")
    for pre in query.get("preconditions", []):
        # pre is a function: bw -> SMT expr
        print(f"(assert {pre(bw)})")
    print(f"(assert {query['negated_assertion'](bw)})")
    print("(check-sat)")


def shift_amount(k, bw):
    return f"(_ bv{k} {bw})"


def half_bw_pow(bw):
    """Return SMT expression for 2^{bw-1}."""
    return f"(_ bv{1 << (bw - 1)} {bw})"


def quarter_bw_pow(bw):
    """Return SMT expression for 2^{bw-2}."""
    return f"(_ bv{1 << (bw - 2)} {bw})"


QUERIES = {
    "bvxor-cancel": {
        "name": "(a XOR b) XOR b = a",
        "vars": ["a", "b"],
        "negated_assertion":
            lambda bw: "(distinct (bvxor (bvxor a b) b) a)",
    },
    "demorgan": {
        "name": "~(a & b) = ~a | ~b",
        "vars": ["a", "b"],
        "negated_assertion":
            lambda bw:
            "(distinct (bvnot (bvand a b)) (bvor (bvnot a) (bvnot b)))",
    },
    "bvnot-involution": {
        "name": "~~a = a",
        "vars": ["a"],
        "negated_assertion":
            lambda bw: "(distinct (bvnot (bvnot a)) a)",
    },
    "shift-identity": {
        "name": "(2x)>>1 = x for x < 2^(bw-1)",
        "vars": ["x"],
        "preconditions": [
            lambda bw: f"(bvult x {half_bw_pow(bw)})",
        ],
        "negated_assertion":
            lambda bw: (
                f"(distinct "
                f"(bvlshr (bvshl x {shift_amount(1, bw)}) "
                f"{shift_amount(1, bw)}) x)"
            ),
    },
    "compound-shift": {
        "name": "((a+b)>>1) = ((b+a)>>1)",
        "vars": ["a", "b"],
        "negated_assertion":
            lambda bw: (
                f"(distinct "
                f"(bvlshr (bvadd a b) {shift_amount(1, bw)}) "
                f"(bvlshr (bvadd b a) {shift_amount(1, bw)}))"
            ),
    },
    "toom-scaled": {
        "name": "((a+b)-(a-b))>>1 = b for b < 2^(bw-1)",
        "vars": ["a", "b"],
        "preconditions": [
            lambda bw: f"(bvult b {half_bw_pow(bw)})",
        ],
        "negated_assertion":
            lambda bw: (
                f"(distinct "
                f"(bvlshr (bvsub (bvadd a b) (bvsub a b)) "
                f"{shift_amount(1, bw)}) b)"
            ),
    },
    "toom-distrib": {
        "name": "((a+b)+(c+d))>>2 = ((a+c)+(b+d))>>2",
        "vars": ["a", "b", "c", "d"],
        "negated_assertion":
            lambda bw: (
                f"(distinct "
                f"(bvlshr (bvadd (bvadd a b) (bvadd c d)) "
                f"{shift_amount(2, bw)}) "
                f"(bvlshr (bvadd (bvadd a c) (bvadd b d)) "
                f"{shift_amount(2, bw)}))"
            ),
    },
}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--query", required=True, choices=list(QUERIES.keys()))
    p.add_argument("--bw", type=int, default=16)
    args = p.parse_args()
    emit(QUERIES[args.query], args.bw)


if __name__ == "__main__":
    main()
