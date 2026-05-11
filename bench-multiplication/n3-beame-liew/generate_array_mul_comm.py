#!/usr/bin/env python3
"""
Generate the CNF for the commutativity assertion a*b = b*a on an n-bit
array multiplier.

This is a self-contained DIMACS generator for the Beame-Liew N3 study.
We produce two array multiplier circuits (a*b giving c, b*a giving d),
and the negation of c=d (so the formula is UNSAT iff multiplication
commutes, which it does, so the formula is UNSAT).

Layout (variables numbered from 1, DIMACS convention):
  a[0..n-1]       : input a bits
  b[0..n-1]       : input b bits
  c[0..2n-1]      : output c = a*b bits
  d[0..2n-1]      : output d = b*a bits
  plus internal partial-product and adder variables.

The array multiplier generates partial products pp[i][j] = a[i] AND b[j]
and sums them column-wise with full adders in an array (ripple-carry)
arrangement. Same for b*a with inputs swapped.

Finally we enforce "c != d" by (at least one bit differs).

Usage: generate_array_mul_comm.py N > out.cnf
"""

import sys


class CnfBuilder:
    def __init__(self):
        self.next_var = 1
        self.clauses = []

    def new_var(self):
        v = self.next_var
        self.next_var += 1
        return v

    def add_clause(self, lits):
        # lits is list of ints (positive = var, negative = neg var)
        self.clauses.append(list(lits))

    def and_gate(self, x, y):
        """Return a new variable z with z <-> x AND y."""
        z = self.new_var()
        # z -> x, z -> y, (not x or not y) -> not z
        self.add_clause([-z, x])
        self.add_clause([-z, y])
        self.add_clause([z, -x, -y])
        return z

    def xor3(self, a, b, c):
        """Return a new variable s = a XOR b XOR c (sum bit of full adder)."""
        s = self.new_var()
        # For each assignment of (a,b,c), force s to the correct parity.
        for av in (False, True):
            for bv in (False, True):
                for cv in (False, True):
                    parity = av ^ bv ^ cv
                    # Clause: (a=av AND b=bv AND c=cv) -> s=parity
                    # <=> NOT(a=av) OR NOT(b=bv) OR NOT(c=cv) OR (s=parity)
                    clause = [
                        -a if av else a,
                        -b if bv else b,
                        -c if cv else c,
                        s if parity else -s,
                    ]
                    self.add_clause(clause)
        return s

    def maj3(self, a, b, c):
        """Return a new variable co = majority(a, b, c) (carry-out of full adder)."""
        co = self.new_var()
        for av in (False, True):
            for bv in (False, True):
                for cv in (False, True):
                    count = int(av) + int(bv) + int(cv)
                    maj_val = count >= 2
                    clause = [
                        -a if av else a,
                        -b if bv else b,
                        -c if cv else c,
                        co if maj_val else -co,
                    ]
                    self.add_clause(clause)
        return co

    def half_adder(self, a, b):
        """Return (sum, carry) for half-adder of a + b."""
        s = self.new_var()
        # s = a XOR b
        self.add_clause([-s, a, b])
        self.add_clause([-s, -a, -b])
        self.add_clause([s, -a, b])
        self.add_clause([s, a, -b])
        co = self.and_gate(a, b)
        return s, co

    def full_adder(self, a, b, ci):
        s = self.xor3(a, b, ci)
        co = self.maj3(a, b, ci)
        return s, co

    def array_multiplier(self, a_bits, b_bits):
        """Return the 2n output bits of the array multiplier a*b."""
        n = len(a_bits)
        assert len(b_bits) == n
        # Partial products: pp[i][j] = a[i] AND b[j], bit weight i+j.
        # Row-sum array multiplier: row 0 is pp[0][*]; each subsequent
        # row i adds pp[i][*] to the running sum.
        # Working accumulator: row_sum[k] for k = 0 .. 2n-1.
        # We use the standard shift-add structure.
        pp = [[self.and_gate(a_bits[i], b_bits[j]) for j in range(n)]
              for i in range(n)]

        # Initialise accumulator with pp[0][*]:
        ZERO = self.new_var()
        self.add_clause([-ZERO])  # ZERO is false
        acc = [ZERO] * (2 * n)
        for j in range(n):
            acc[j] = pp[0][j]
        # Now add pp[i][*] (shifted by i) for i = 1 .. n-1
        for i in range(1, n):
            new_acc = list(acc)
            carry = ZERO
            for j in range(n):
                # Column i+j: acc[i+j] + pp[i][j] + carry
                col = i + j
                s, co = self.full_adder(acc[col], pp[i][j], carry)
                new_acc[col] = s
                carry = co
            # Propagate final carry through remaining columns.
            col = i + n
            while col < 2 * n:
                # acc[col] + carry
                s, co = self.half_adder(acc[col], carry)
                new_acc[col] = s
                carry = co
                col += 1
            acc = new_acc
        return acc

    def add_neq(self, xs, ys):
        """Assert that xs != ys as bit-vectors: at least one bit differs."""
        assert len(xs) == len(ys)
        n = len(xs)
        # For each bit, a literal that's true iff xs[i] != ys[i].
        diff_lits = []
        for x, y in zip(xs, ys):
            d = self.new_var()
            # d <-> (x XOR y)
            self.add_clause([-d, x, y])
            self.add_clause([-d, -x, -y])
            self.add_clause([d, -x, y])
            self.add_clause([d, x, -y])
            diff_lits.append(d)
        # At least one difference: OR of diff_lits.
        self.add_clause(diff_lits)

    def write(self, out):
        out.write("p cnf {} {}\n".format(self.next_var - 1, len(self.clauses)))
        for cl in self.clauses:
            out.write(" ".join(str(lit) for lit in cl) + " 0\n")


def build_commutativity_cnf(n):
    """Build the CNF for a*b = b*a on an n-bit array multiplier."""
    cnf = CnfBuilder()
    a = [cnf.new_var() for _ in range(n)]
    b = [cnf.new_var() for _ in range(n)]
    c = cnf.array_multiplier(a, b)  # a*b
    d = cnf.array_multiplier(b, a)  # b*a
    cnf.add_neq(c, d)  # Negation of commutativity.
    return cnf, a, b, c, d


def main():
    if len(sys.argv) != 2:
        print("usage: generate_array_mul_comm.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf, a, b, c, d = build_commutativity_cnf(n)
    # Emit variable-to-role mapping as a comment block.
    print(f"c array multiplier commutativity, n={n}")
    print(f"c a bits: {' '.join(str(v) for v in a)}")
    print(f"c b bits: {' '.join(str(v) for v in b)}")
    print(f"c c bits (a*b): {' '.join(str(v) for v in c)}")
    print(f"c d bits (b*a): {' '.join(str(v) for v in d)}")
    cnf.write(sys.stdout)


if __name__ == "__main__":
    main()
