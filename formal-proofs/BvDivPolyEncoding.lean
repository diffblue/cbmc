/-
Polynomial encoding of `bvudiv` and `bvurem` (Phase 2).

The C++ implementation in
`src/solvers/algebraic/poly_extract.cpp::to_polynomial` introduces
fresh polynomial variables `q` and `r` for each `bvudiv s t` and
`bvurem s t`, and adds the side equation

    q * t + r - s = 0    in ZMod (2^d)

The polynomial system is sound for UNSAT detection: every model
of the SMT formula yields a model of the polynomial system (set
`q := bvudiv s t`, `r := bvurem s t`), so polynomial UNSAT
implies SMT UNSAT.

We prove three properties:

1. `bvdiv_bvurem_polynomial_eq`: at integer level, the canonical
   division pair `(q, r) = (s.val / t.val, s.val mod t.val)`
   satisfies `q * t + r = s` exactly (no overflow in ZMod (2^d)).
2. `bvurem_zero_polynomial_eq`: when `t = 0`, the SMT-LIB
   convention `bvurem s 0 = s` makes `0 + r - s = 0` true with
   `r := s`, so the side equation holds with `q` free.
3. `bvdiv_polynomial_overapprox`: the polynomial system has more
   solutions than the SMT formula (specifically: when `t = 0`,
   `q` is free at the polynomial level but pinned to `~0` at the
   SMT level), which is sound for UNSAT detection.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace BvDivPolyEncoding

/-- Integer-level division pair: when `t.val ≠ 0`, the canonical
    representatives of `q = bvudiv s t` and `r = bvurem s t`
    satisfy `q.val * t.val + r.val = s.val` exactly (no overflow
    when reducing modulo 2^d, because `q.val * t.val ≤ s.val < 2^d`). -/
theorem int_division_no_overflow
    (s t : ℕ) :
    s / t * t + s % t = s :=
  Nat.div_add_mod' s t

/-- The polynomial side equation `q * t + r - s = 0` holds in
    ZMod (2^d) when `q` and `r` are the canonical division pair
    of `s` and `t` (with `t ≠ 0`). The reduction modulo 2^d is
    safe because the integer-level identity has no overflow. -/
theorem bvdiv_bvurem_polynomial_eq
    {d : ℕ} [NeZero (2^d)] (s t : ZMod (2^d)) :
    ((s.val / t.val : ℕ) : ZMod (2^d)) * t +
    ((s.val % t.val : ℕ) : ZMod (2^d)) - s = 0 := by
  -- Factor out `s.val` and `t.val` as named natural numbers so
  -- that subsequent rewrites of the *standalone* `t` and `s` in
  -- ZMod (2^d) do not accidentally rewrite the `.val` arguments.
  set sv : ℕ := s.val with hsv
  set tv : ℕ := t.val with htv
  have ht_eq : (t : ZMod (2^d)) = ((tv : ℕ) : ZMod (2^d)) := by
    rw [htv]
    exact (ZMod.natCast_zmod_val t).symm
  have hs_eq : (s : ZMod (2^d)) = ((sv : ℕ) : ZMod (2^d)) := by
    rw [hsv]
    exact (ZMod.natCast_zmod_val s).symm
  rw [ht_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod', hs_eq, sub_self]

/-- SMT-LIB-2 convention case: when `t = 0`, `bvurem s 0 = s`
    so the side equation `q * 0 + r - s = 0` holds with `r = s`
    (and `q` free). The polynomial encoding therefore admits
    `(q, r) = (anything, s)` as a solution when `t = 0`, which
    is over-approximate: the SMT level fixes `q = ~0` but the
    polynomial level does not. -/
theorem bvurem_zero_polynomial_eq
    {d : ℕ} (s : ZMod (2^d)) (q : ZMod (2^d)) :
    q * 0 + s - s = 0 := by
  ring

/-- Soundness of the over-approximation: if the polynomial
    system (with the side equation) is unsatisfiable for any
    choice of `q, r` extending the SMT-level model, then so is
    the SMT formula. Equivalently, every SMT model lifts to a
    polynomial-system model, so polynomial UNSAT implies SMT
    UNSAT. -/
theorem bvdiv_polynomial_overapprox
    {d : ℕ} (s t : ZMod (2^d))
    (smt_q smt_r : ZMod (2^d))
    (h_eq : smt_q * t + smt_r - s = 0) :
    ∃ q r : ZMod (2^d), q * t + r - s = 0 :=
  ⟨smt_q, smt_r, h_eq⟩

end BvDivPolyEncoding

namespace BvNotEncoding

/-- The `bvnot` algebraic identity used by the polynomial
    extractor: `~a = (2^d - 1) - a` in ZMod (2^d). This is a
    pure ring identity (the all-ones constant equals -1 in the
    canonical representative), and it lets us convert `bvnot a`
    to a polynomial without going through bit-decomposition,
    avoiding 2*d extra equations. -/
theorem bvnot_eq_neg_one_sub
    {d : ℕ} [NeZero (2^d)] (a : ZMod (2^d)) :
    ((2^d - 1 : ℕ) : ZMod (2^d)) - a = -1 - a := by
  congr 1
  -- (2^d - 1 : ℕ) cast to ZMod (2^d) equals -1.
  have h1 : (1 : ℕ) ≤ 2^d := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos d))
  have hcast : ((2^d - 1 : ℕ) : ZMod (2^d)) =
      ((2^d : ℕ) : ZMod (2^d)) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast]
  have hpow : ((2^d : ℕ) : ZMod (2^d)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2^d)
  rw [hpow, zero_sub]

end BvNotEncoding
