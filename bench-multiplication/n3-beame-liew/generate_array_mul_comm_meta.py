#!/usr/bin/env python3
"""
Like generate_array_mul_comm.py, but also produces a metadata record
that tags every variable with its role in the array multiplier:

  - ("a_bit", i)        : input bit a[i]
  - ("b_bit", i)        : input bit b[i]
  - ("pp_c", i, j)      : partial product a[i] AND b[j] in the a*b multiplier
  - ("pp_d", i, j)      : partial product b[i] AND a[j] in the b*a multiplier
  - ("acc_c", row, col) : accumulator sum bit after row `row` at column `col` in a*b
  - ("cry_c", row, col) : carry bit out of column `col` during row `row` in a*b
  - ("acc_d", row, col) : similarly for b*a
  - ("cry_d", row, col)
  - ("zero",)           : the hard-coded false constant
  - ("diff", k)         : "bit k of c differs from bit k of d" (for neq assertion)

Phase 2 uses this metadata to split the CNF into per-strip slices and to
identify carry-state boundaries between strips.
"""

import sys


class CnfBuilderMeta:
    def __init__(self):
        self.next_var = 1
        self.clauses = []
        self.meta = {}  # var -> role tuple

    def new_var(self, role):
        v = self.next_var
        self.next_var += 1
        self.meta[v] = role
        return v

    def add_clause(self, lits):
        self.clauses.append(list(lits))

    def and_gate(self, x, y, role):
        z = self.new_var(role)
        self.add_clause([-z, x])
        self.add_clause([-z, y])
        self.add_clause([z, -x, -y])
        return z

    def xor_gate(self, x, y, role):
        z = self.new_var(role)
        self.add_clause([-z, x, y])
        self.add_clause([-z, -x, -y])
        self.add_clause([z, -x, y])
        self.add_clause([z, x, -y])
        return z

    def xor3(self, a, b, c, role):
        s = self.new_var(role)
        for av in (False, True):
            for bv in (False, True):
                for cv in (False, True):
                    parity = av ^ bv ^ cv
                    self.add_clause([
                        -a if av else a,
                        -b if bv else b,
                        -c if cv else c,
                        s if parity else -s,
                    ])
        return s

    def maj3(self, a, b, c, role):
        co = self.new_var(role)
        for av in (False, True):
            for bv in (False, True):
                for cv in (False, True):
                    count = int(av) + int(bv) + int(cv)
                    maj_val = count >= 2
                    self.add_clause([
                        -a if av else a,
                        -b if bv else b,
                        -c if cv else c,
                        co if maj_val else -co,
                    ])
        return co

    def half_adder(self, a, b, role_s, role_c):
        s = self.xor_gate(a, b, role_s)
        co = self.and_gate(a, b, role_c)
        return s, co

    def full_adder(self, a, b, ci, role_s, role_c):
        s = self.xor3(a, b, ci, role_s)
        co = self.maj3(a, b, ci, role_c)
        return s, co

    def array_multiplier(self, a_bits, b_bits, side):
        """Return the 2n output bits. side is 'c' (a*b) or 'd' (b*a)."""
        n = len(a_bits)
        assert len(b_bits) == n

        pp_tag = "pp_c" if side == "c" else "pp_d"
        acc_tag = "acc_c" if side == "c" else "acc_d"
        cry_tag = "cry_c" if side == "c" else "cry_d"

        pp = [[self.and_gate(a_bits[i], b_bits[j], (pp_tag, i, j))
               for j in range(n)] for i in range(n)]

        ZERO = self.new_var(("zero", side))
        self.add_clause([-ZERO])
        acc = [ZERO] * (2 * n)
        for j in range(n):
            acc[j] = pp[0][j]

        for i in range(1, n):
            new_acc = list(acc)
            carry = ZERO
            for j in range(n):
                col = i + j
                s, co = self.full_adder(
                    acc[col], pp[i][j], carry,
                    (acc_tag, i, col), (cry_tag, i, col),
                )
                new_acc[col] = s
                carry = co
            col = i + n
            while col < 2 * n:
                s, co = self.half_adder(
                    acc[col], carry,
                    (acc_tag, i, col), (cry_tag, i, col),
                )
                new_acc[col] = s
                carry = co
                col += 1
            acc = new_acc

        return acc

    def add_neq(self, xs, ys, side_tag="diff"):
        assert len(xs) == len(ys)
        diff_lits = []
        for i, (x, y) in enumerate(zip(xs, ys)):
            d = self.new_var((side_tag, i))
            self.add_clause([-d, x, y])
            self.add_clause([-d, -x, -y])
            self.add_clause([d, -x, y])
            self.add_clause([d, x, -y])
            diff_lits.append(d)
        self.add_clause(diff_lits)

    def write(self, out):
        out.write("p cnf {} {}\n".format(self.next_var - 1, len(self.clauses)))
        for cl in self.clauses:
            out.write(" ".join(str(lit) for lit in cl) + " 0\n")


def build_commutativity_cnf_meta(n):
    cnf = CnfBuilderMeta()
    a = [cnf.new_var(("a_bit", i)) for i in range(n)]
    b = [cnf.new_var(("b_bit", i)) for i in range(n)]
    c = cnf.array_multiplier(a, b, side="c")
    d = cnf.array_multiplier(b, a, side="d")
    cnf.add_neq(c, d)
    return cnf, a, b, c, d


def role_col(role):
    """Return the column index associated with a role, or None if not column-indexed."""
    if role is None:
        return None
    tag = role[0]
    if tag in ("a_bit", "b_bit"):
        return None  # inputs are not strictly "columnar"
    if tag in ("pp_c", "pp_d"):
        # partial product at (i, j), contributes to column i+j
        return role[1] + role[2]
    if tag in ("acc_c", "acc_d", "cry_c", "cry_d"):
        # role = (tag, row, col)
        return role[2]
    if tag == "diff":
        return role[1]
    if tag == "zero":
        return None
    return None


def main():
    if len(sys.argv) != 2:
        print("usage: generate_array_mul_comm_meta.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf, a, b, c, d = build_commutativity_cnf_meta(n)
    # Emit CNF with per-variable role as comments.
    print(f"c array multiplier commutativity, n={n}")
    print(f"c a bits: {' '.join(str(v) for v in a)}")
    print(f"c b bits: {' '.join(str(v) for v in b)}")
    print(f"c c bits (a*b): {' '.join(str(v) for v in c)}")
    print(f"c d bits (b*a): {' '.join(str(v) for v in d)}")
    for v, role in sorted(cnf.meta.items()):
        print(f"c v{v}: {role}")
    cnf.write(sys.stdout)


if __name__ == "__main__":
    main()
