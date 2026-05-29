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

/-! ## Rewrite 5: bvule / bvult relations with bvurem

    SMT-LIB's `bvule (bvurem A y) y` is defined on canonical
    representatives `.val`. We capture the soundness of the
    parse-time rewrites:

      bvule (bvurem A y) y = ite (= y 0) (= A 0) true
      bvult (bvurem A y) y = ¬(= y 0)

    The first is conditional: when y = 0, bvurem A 0 = A, so
    bvule A 0 holds iff A = 0; when y ≠ 0, bvurem A y < y
    strictly so bvule holds. The second is similar but stricter:
    when y = 0, bvult A 0 is false (no unsigned value is < 0).
-/

@[simp] lemma bvurem_zero_right {n : ℕ} [NeZero n] (A : ZMod n) :
    bvurem A 0 = A := by
  unfold bvurem; simp

/-- Soundness of the parse-time rewrite
    `bvule (bvurem A y) y → ite (= y 0) (= A 0) true`. -/
theorem bvule_bvurem_self {n : ℕ} [NeZero n] (A y : ZMod n) :
    ((bvurem A y).val ≤ y.val) ↔
    (if y = 0 then A = 0 else True) := by
  by_cases h : y = 0
  · -- y = 0: bvurem A 0 = A, val_zero gives goal A.val ≤ 0 ↔ A = 0
    rw [if_pos h]
    constructor
    · intro hle
      rw [h, bvurem_zero_right, ZMod.val_zero] at hle
      exact ZMod.val_eq_zero A |>.mp (Nat.le_zero.mp hle)
    · intro hA
      rw [h, bvurem_zero_right, hA, ZMod.val_zero]
  · -- y ≠ 0: bvurem A y < y strictly, so ≤ holds
    rw [if_neg h]
    apply iff_of_true _ trivial
    -- Now prove (bvurem A y).val ≤ y.val
    unfold bvurem
    simp [h]
    have hpos : 0 < y.val := by
      rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]; exact h
    have hbound : A.val % y.val < y.val := Nat.mod_lt A.val hpos
    have hyn : y.val < n := y.val_lt
    have hmod : A.val % y.val % n = A.val % y.val :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hbound (le_of_lt hyn))
    omega

/-- Soundness of the parse-time rewrite
    `bvult (bvurem A y) y → ¬(= y 0)`. -/
theorem bvult_bvurem_self {n : ℕ} [NeZero n] (A y : ZMod n) :
    ((bvurem A y).val < y.val) ↔ y ≠ 0 := by
  unfold bvurem
  by_cases h : y = 0
  · simp [h]
  · simp [h]
    have hpos : 0 < y.val := by
      rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]; exact h
    have hbound : A.val % y.val < y.val := Nat.mod_lt A.val hpos
    have hyn : y.val < n := y.val_lt
    have hmod : A.val % y.val % n = A.val % y.val :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hbound (le_of_lt hyn))
    omega

/-! ## Rewrite 6: ite-distribution and constant-divisor folding -/

/-- ite-distribution: `bvudiv X (if c then Y else Z) =
    if c then bvudiv X Y else bvudiv X Z`. Trivially sound by
    case analysis on the if-condition. -/
theorem bvudiv_ite_distribution {n : ℕ} [NeZero n]
    (X Y Z : ZMod n) (c : Prop) [Decidable c] :
    bvudiv X (if c then Y else Z) =
    (if c then bvudiv X Y else bvudiv X Z) := by
  by_cases h : c <;> simp [h]

/-- ite-distribution for bvurem: same pattern. -/
theorem bvurem_ite_distribution {n : ℕ} [NeZero n]
    (X Y Z : ZMod n) (c : Prop) [Decidable c] :
    bvurem X (if c then Y else Z) =
    (if c then bvurem X Y else bvurem X Z) := by
  by_cases h : c <;> simp [h]

/-- (bvudiv (bvurem A y) y) = ite(= y 0, -1, 0).
    Cancellation: when y ≠ 0, bvurem A y < y so dividing by y
    gives 0; when y = 0, bvurem A 0 = A and bvudiv A 0 = -1. -/
theorem bvudiv_bvurem_self {n : ℕ} [NeZero n] (A y : ZMod n) :
    bvudiv (bvurem A y) y =
    (if y = 0 then (-1 : ZMod n) else 0) := by
  unfold bvudiv bvurem
  by_cases h : y = 0
  · simp [h]
  · simp [h]
    have hpos : 0 < y.val := by
      rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]; exact h
    have hbound : A.val % y.val < y.val := Nat.mod_lt A.val hpos
    have hyn : y.val < n := y.val_lt
    have hmod : A.val % y.val % n = A.val % y.val :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hbound (le_of_lt hyn))
    rw [hmod, Nat.div_eq_of_lt hbound]
    simp

end DivisionRewrites
