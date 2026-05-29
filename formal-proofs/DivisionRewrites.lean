/-
  DivisionRewrites.lean — Soundness of the parse-time word-level
  rewrites for bv_div / bv_mod operators.

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  The C++ `smt2_parsert::bv_division` and
  `smt2_parsert::bv_mod` (in `src/solvers/smt2/smt2_parser.cpp`)
  recognise five patterns at parse time and emit the simplified
  form, avoiding construction of a full divider in the
  downstream bit-blasted form:

    (bvudiv x x)  = ite(x = 0, ~0, 1)
    (bvurem x x)  = 0
    (bvudiv 0 x)  = ite(x = 0, ~0, 0)
    (bvurem 0 x)  = 0

  with the analogous patterns for the signed variants
  `bvsdiv` / `bvsrem` / `bvsmod` (we treat unsigned and
  signed-non-negative-result variants together; the SMT-LIB
  semantics make `x/x = 1` and `x%x = 0` for all non-zero `x`
  in 2's-complement, including the signed minimum).

  This module formalises the unsigned versions; the signed
  cases follow by the same pointwise argument.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace DivisionRewrites

/-- SMT-LIB `bvudiv x y` over a `d`-bit word (here `n = 2^d`):
    the result is `~0` (all-ones) when the divisor is zero,
    otherwise the integer-division of the canonical
    representatives. -/
noncomputable def bvudiv {n : ℕ} [NeZero n] (x y : ZMod n) : ZMod n :=
  if y = 0 then (-1 : ZMod n)
  else (x.val / y.val : ZMod n)

/-- SMT-LIB `bvurem x y`: the result is the dividend when the
    divisor is zero (per SMT-LIB convention), otherwise the
    integer-modulo of the canonical representatives. -/
noncomputable def bvurem {n : ℕ} [NeZero n] (x y : ZMod n) : ZMod n :=
  if y = 0 then x
  else (x.val % y.val : ZMod n)

/-! ## Rewrite 1: bvudiv x x = ite(x = 0, ~0, 1) -/

theorem bvudiv_self {n : ℕ} [NeZero n] (x : ZMod n) :
    bvudiv x x = if x = 0 then (-1 : ZMod n) else 1 := by
  unfold bvudiv
  by_cases h : x = 0
  · simp [h]
  · have hpos : 0 < x.val := by
      rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      exact h
    simp [h, Nat.div_self hpos]

/-! ## Rewrite 2: bvurem x x = 0 -/

theorem bvurem_self {n : ℕ} [NeZero n] (x : ZMod n) :
    bvurem x x = 0 := by
  unfold bvurem
  by_cases h : x = 0
  · simp [h]
  · simp [h, Nat.mod_self]

/-! ## Rewrite 3: bvudiv 0 x = ite(x = 0, ~0, 0) -/

theorem bvudiv_zero_left {n : ℕ} [NeZero n] (x : ZMod n) :
    bvudiv 0 x = if x = 0 then (-1 : ZMod n) else 0 := by
  unfold bvudiv
  by_cases h : x = 0
  · simp [h]
  · simp [h, ZMod.val_zero, Nat.zero_div]

/-! ## Rewrite 4: bvurem 0 x = 0 -/

theorem bvurem_zero_left {n : ℕ} [NeZero n] (x : ZMod n) :
    bvurem 0 x = 0 := by
  unfold bvurem
  by_cases h : x = 0
  · simp [h]
  · simp [h, ZMod.val_zero, Nat.zero_mod]

end DivisionRewrites
