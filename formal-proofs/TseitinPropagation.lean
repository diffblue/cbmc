/-
Soundness of the Tseitin-style boolean propagation rules used by
`src/solvers/flattening/tseitin_propagation.cpp`.

The C++ implementation runs forward simplification and backward
inversion to a fixed point on a graph of boolean-symbol
definitions. Each per-rule inversion step is sound by classical
propositional reasoning. We mechanise the rules at the level of
booleans (`Bool`) where each propagation rule is provable by a
two-case `decide`.

For the bit-vector level rules (e.g., emit `(equal X Y)` as an
implied polynomial equality when a bool-sym tied to it is forced
to `1`), the soundness reduces to: if `b ↔ (X = Y)` and we can
prove `b = true`, then `X = Y`. This is again classical.
-/

import Mathlib.Tactic

namespace TseitinPropagation

/-- Backward inversion of `bitnot`: `¬b = v ⟹ b = ¬v`. -/
theorem bitnot_inversion (b : Bool) (v : Bool) :
    (!b) = v → b = !v := by
  cases b <;> cases v <;> decide

/-- Backward inversion of `bitor` to 0: `(b₁ ∨ b₂) = false ⟹
    b₁ = false ∧ b₂ = false`. -/
theorem bitor_zero_inversion (b1 b2 : Bool) :
    (b1 || b2) = false → b1 = false ∧ b2 = false := by
  cases b1 <;> cases b2 <;> decide

/-- Backward inversion of `bitand` to 1: `(b₁ ∧ b₂) = true ⟹
    b₁ = true ∧ b₂ = true`. -/
theorem bitand_one_inversion (b1 b2 : Bool) :
    (b1 && b2) = true → b1 = true ∧ b2 = true := by
  cases b1 <;> cases b2 <;> decide

/-- Backward inversion of `bitxor`: `(b₁ ⊕ b₂) = v ⟹ b₂ = (v ⊕ b₁)`
    when `b₁` is known. -/
theorem bitxor_inversion (b1 b2 v : Bool) :
    (xor b1 b2) = v → b2 = xor v b1 := by
  cases b1 <;> cases b2 <;> cases v <;> decide

/-- Backward inversion of equality: `(b₁ = b₂) = true ⟹ b₁ = b₂`. -/
theorem eq_true_inversion (b1 b2 : Bool) :
    decide (b1 = b2) = true → b1 = b2 := by
  cases b1 <;> cases b2 <;> decide

/-- Backward inversion of equality (false case): `(b₁ = b₂) = false
    ⟹ b₁ = ¬b₂`. -/
theorem eq_false_inversion (b1 b2 : Bool) :
    decide (b1 = b2) = false → b1 = !b2 := by
  cases b1 <;> cases b2 <;> decide

/-- Forward evaluation soundness for `bitor`: each evaluation rule
    produces the correct truth value. -/
theorem bitor_eval (b1 b2 : Bool) (h : b1 = true) :
    (b1 || b2) = true := by
  cases b1 <;> cases b2 <;> simp_all

theorem bitor_eval_both_false (b1 b2 : Bool)
    (h1 : b1 = false) (h2 : b2 = false) : (b1 || b2) = false := by
  cases b1 <;> cases b2 <;> simp_all

/-- The bit-vector emission rule: when a boolean variable `b` is
    proved to be `true` and we have the Tseitin definition
    `b ↔ (X = Y)` (with `X, Y : ℕ`), we may conclude `X = Y`. -/
theorem bv_eq_emission {X Y : ℕ} (b : Bool)
    (def_iff : b ↔ X = Y) (h : b = true) : X = Y := by
  have : (b = true) ↔ X = Y := by
    constructor
    · intro hb; exact def_iff.mp (by simp [hb])
    · intro hxy; simpa using def_iff.mpr hxy
  exact this.mp h

/-- The bit-vector emission rule for the `false` case: when a
    boolean variable `b` is proved to be `false` and we have the
    Tseitin definition `b ↔ (X = Y)`, we may conclude `X ≠ Y`. -/
theorem bv_neq_emission {X Y : ℕ} (b : Bool)
    (def_iff : b ↔ X = Y) (h : b = false) : X ≠ Y := by
  intro hxy
  have : b = true := by simp [def_iff.mpr hxy]
  rw [this] at h
  exact Bool.noConfusion h

/-- Concatenation polynomial encoding: for unsigned bit-vectors,
    `concat(a, b)` of widths `(n, m)` represents the integer
    `a * 2^m + b` in `(n+m)`-bit unsigned. The polynomial extractor
    in `src/solvers/algebraic/poly_extract.cpp::to_polynomial`
    encodes concat using exactly this formula. Soundness of the
    polynomial encoding follows from the integer-level identity
    and the fact that `(a * 2^m + b) mod 2^(n+m) = a * 2^m + b`
    when `a < 2^n` and `b < 2^m`. -/
theorem concat_polynomial_encoding (n m : ℕ) (a b : ℕ)
    (ha : a < 2 ^ n) (hb : b < 2 ^ m) :
    a * 2 ^ m + b < 2 ^ (n + m) := by
  rw [pow_add]
  calc a * 2 ^ m + b
      < a * 2 ^ m + 2 ^ m := by omega
    _ = (a + 1) * 2 ^ m := by ring
    _ ≤ 2 ^ n * 2 ^ m := by
        apply Nat.mul_le_mul_right
        omega

end TseitinPropagation
