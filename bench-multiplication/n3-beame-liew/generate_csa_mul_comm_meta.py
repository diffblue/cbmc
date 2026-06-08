#!/usr/bin/env python3
"""
Carry-save-array multiplier commutativity CNF with metadata.

Uses CSA (not ripple-carry within rows) to match Beame-Liew §3.1's
(n+1) x (n+1) adder grid in spirit.

Variable roles:
  ("a_bit", i)        : input bit a[i]
  ("b_bit", i)        : input bit b[i]
  ("pp_c", i, j)      : partial product a[j] AND b[i] (row i, col-offset j; weight 2^(i+j))
  ("pp_d", i, j)      : partial product b[j] AND a[i]
  ("d_c", i, col)     : CSA sum bit at row i, column col (a*b)
  ("c_c", i, col)     : CSA carry bit at row i, column col (a*b)
  ("d_d", i, col)     : CSA sum bit at row i, column col (b*a)
  ("c_d", i, col)     : CSA carry bit at row i, column col (b*a)
  ("cpa_c", col)      : final CPA sum bit at column col (a*b)
  ("cpa_cry_c", col)  : final CPA carry-out at column col (a*b)
  ("cpa_d", col)      : final CPA sum bit (b*a)
  ("cpa_cry_d", col)  : final CPA carry-out (b*a)
  ("zero", side)      : hard-coded false
  ("diff", k)         : diff indicator between c[k] and d[k]

CSA recurrence (rows i = 1..n-1, cols 0..2n-1):
  t_in = pp[(i, col-i)]    if 0 <= col-i < n else 0
  d_in = d[(i-1, col)]
  c_in = c[(i-1, col-1)]   if col >= 1 else 0
  d[(i, col)] = XOR3(t_in, d_in, c_in)
  c[(i, col)] = MAJ3(t_in, d_in, c_in)

Row 0:
  d[(0, col)] = pp[(0, col)]  for col in [0, n-1]
  d[(0, col)] = 0             for col in [n, 2n-1]
  c[(0, col)] = 0

Final ripple CPA:
  out[0] = d[(n-1, 0)]
  for col in 1..2n-1:
    s_in = d[(n-1, col)]
    c_in = c[(n-1, col-1)]
    out[col] = XOR3(s_in, c_in, prev_carry)
    new_carry = MAJ3(s_in, c_in, prev_carry)
"""

import sys


class CsaBuilder:
    def __init__(self):
        self.next_var = 1
        self.clauses = []
        self.meta = {}
        self._zero_var = None  # set by csa_multiplier (shared across sides)

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

    def xor3(self, a, b, c, role):
        # Simplify if any inputs are the ZERO constant (or structurally
        # equal). We track ZERO via roles; check if the var role is
        # ("zero", ...).
        zero_var = self._zero_var
        if a == zero_var:
            return self.xor2(b, c, role) if b != c else zero_var
        if b == zero_var:
            return self.xor2(a, c, role) if a != c else zero_var
        if c == zero_var:
            return self.xor2(a, b, role) if a != b else zero_var
        if a == b:
            return c if c != zero_var else zero_var
        if a == c:
            return b if b != zero_var else zero_var
        if b == c:
            return a if a != zero_var else zero_var
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

    def xor2(self, a, b, role):
        if a == b:
            return self._zero_var
        if a == self._zero_var:
            return b
        if b == self._zero_var:
            return a
        s = self.new_var(role)
        self.add_clause([-s, a, b])
        self.add_clause([-s, -a, -b])
        self.add_clause([s, -a, b])
        self.add_clause([s, a, -b])
        return s

    def maj3(self, a, b, c, role):
        zero_var = self._zero_var
        if a == zero_var:
            return self.and_gate(b, c, role) if b != c else b
        if b == zero_var:
            return self.and_gate(a, c, role) if a != c else a
        if c == zero_var:
            return self.and_gate(a, b, role) if a != b else a
        if a == b:
            return a
        if a == c:
            return a
        if b == c:
            return b
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

    def csa_multiplier(self, x_bits, y_bits, side):
        """CSA multiplier with final ripple CPA.

        x_bits, y_bits are the input vectors (LSB first).
        side is 'c' (a*b) or 'd' (b*a).

        pp[(i, j)] = y[i] AND x[j] (row i, col j), weight 2^(i+j).
        """
        n = len(x_bits)
        assert len(y_bits) == n

        pp_tag = "pp_c" if side == "c" else "pp_d"
        d_tag = "d_c" if side == "c" else "d_d"
        c_tag = "c_c" if side == "c" else "c_d"
        cpa_tag = "cpa_c" if side == "c" else "cpa_d"
        cpa_cry_tag = "cpa_cry_c" if side == "c" else "cpa_cry_d"
        zero_tag = ("zero", side)

        if self._zero_var is None:
            self._zero_var = self.new_var(("zero", "shared"))
            self.add_clause([-self._zero_var])
        ZERO = self._zero_var

        # Partial products
        pp = {}
        for i in range(n):
            for j in range(n):
                # pp[(i,j)] = y[i] AND x[j], for side 'c' y=b, x=a.
                # We keep the same (i, j) notation as ripple-carry version,
                # meaning row i (outer) col j (inner), weight 2^(i+j).
                pp[(i, j)] = self.and_gate(
                    y_bits[i], x_bits[j], (pp_tag, i, j)
                )

        # CSA grid: d[(i, col)], c[(i, col)]
        d = {}
        c = {}

        # Row 0
        for col in range(2 * n):
            if col < n:
                # d[(0, col)] = pp[(0, col)]; just alias the pp var
                d[(0, col)] = pp[(0, col)]
            else:
                d[(0, col)] = ZERO
            c[(0, col)] = ZERO

        # Rows i = 1..n-1
        for i in range(1, n):
            for col in range(2 * n):
                t_in = pp[(i, col - i)] if 0 <= col - i < n else ZERO
                d_in = d[(i - 1, col)]
                c_in = c[(i - 1, col - 1)] if col >= 1 else ZERO
                d[(i, col)] = self.xor3(t_in, d_in, c_in, (d_tag, i, col))
                c[(i, col)] = self.maj3(t_in, d_in, c_in, (c_tag, i, col))

        # Final ripple CPA: out[col] = d[n-1, col] + c[n-1, col-1] + carry_in
        out = [None] * (2 * n)
        prev_carry = ZERO
        for col in range(2 * n):
            s_in = d[(n - 1, col)]
            c_in = c[(n - 1, col - 1)] if col >= 1 else ZERO
            out[col] = self.xor3(s_in, c_in, prev_carry, (cpa_tag, col))
            prev_carry = self.maj3(
                s_in, c_in, prev_carry, (cpa_cry_tag, col)
            )
        return out

    def add_neq(self, xs, ys, side_tag="diff"):
        assert len(xs) == len(ys)
        diff_lits = []
        for i, (x, y) in enumerate(zip(xs, ys)):
            di = self.new_var((side_tag, i))
            self.add_clause([-di, x, y])
            self.add_clause([-di, -x, -y])
            self.add_clause([di, -x, y])
            self.add_clause([di, x, -y])
            diff_lits.append(di)
        self.add_clause(diff_lits)

    def write(self, out):
        out.write("p cnf {} {}\n".format(
            self.next_var - 1, len(self.clauses)
        ))
        for cl in self.clauses:
            out.write(" ".join(str(lit) for lit in cl) + " 0\n")


def build_commutativity_csa_cnf(n):
    cnf = CsaBuilder()
    a = [cnf.new_var(("a_bit", i)) for i in range(n)]
    b = [cnf.new_var(("b_bit", i)) for i in range(n)]
    c = cnf.csa_multiplier(a, b, side="c")
    d = cnf.csa_multiplier(b, a, side="d")
    cnf.add_neq(c, d)
    return cnf, a, b, c, d


def role_col(role):
    """Return column index for a role, or None."""
    if role is None:
        return None
    tag = role[0]
    if tag in ("a_bit", "b_bit"):
        return None
    if tag in ("pp_c", "pp_d"):
        return role[1] + role[2]
    if tag in ("d_c", "d_d", "c_c", "c_d"):
        return role[2]
    if tag in ("cpa_c", "cpa_d", "cpa_cry_c", "cpa_cry_d"):
        return role[1]
    if tag == "diff":
        return role[1]
    if tag == "zero":
        return None
    return None


def main():
    if len(sys.argv) != 2:
        print("usage: generate_csa_mul_comm_meta.py N", file=sys.stderr)
        sys.exit(1)
    n = int(sys.argv[1])
    cnf, a, b, c, d = build_commutativity_csa_cnf(n)
    print(f"c CSA multiplier commutativity, n={n}")
    print(f"c a bits: {' '.join(str(v) for v in a)}")
    print(f"c b bits: {' '.join(str(v) for v in b)}")
    print(f"c c bits (a*b): {' '.join(str(v) for v in c)}")
    print(f"c d bits (b*a): {' '.join(str(v) for v in d)}")
    for v, role in sorted(cnf.meta.items()):
        print(f"c v{v}: {role}")
    cnf.write(sys.stdout)


if __name__ == "__main__":
    main()
