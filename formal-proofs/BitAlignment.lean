/-
  BitAlignment.lean — Soundness proofs for bit alignment substitutions
  introduced by P2 (parity reasoning).

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/algebraic/poly_extract.cpp`
  (`materialise_bit_alignments`).

  When the polynomial system contains a side equation of the form
  `h - c*x = 0` for a constant power of 2 `c = 2^k` and both `h` and
  `x` are bit-decomposed, the implementation registers the
  substitutions

    b_{h, i}      ↦ 0       for i ∈ [0, k-1]   (low bits zero)
    b_{h, i+k}    ↦ b_{x, i} for i ∈ [0, d-1-k] (shifted bits)

  This Lean module mechanises the soundness of these substitutions.

  Coverage:

    1. (Low bits zero) For h = 2^k * x in Z_{2^d}, bits 0..k-1 of h
       are zero in the standard decomposition.

    2. (Bit shift alignment) For h = 2^k * x, bit i+k of h equals
       bit i of x for i + k < d (and bit i+k of h is irrelevant /
       lost to overflow for i + k ≥ d).

  Both follow from the standard binary expansion of 2^k * x mod 2^d.
-/

import Re4
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace BitAlignment

open Re4

/-! ## (1) Low bits zero

    For h = 2^k * x mod 2^d, bits 0..k-1 of h are zero.
-/

/-- Common helper: `((2^k : ZMod (2^d))).val = 2^k` when `k < d`. -/
private lemma val_two_pow_lt {d k : ℕ} (hk : k < d) :
    ((2 ^ k : ZMod (2 ^ d))).val = 2 ^ k := by
  have h_eq : ((2 : ZMod (2 ^ d)) ^ k) = ((2 ^ k : ℕ) : ZMod (2 ^ d)) := by
    push_cast; rfl
  rw [h_eq, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::materialise_bit_alignments
    (the low-bit-zero substitutions: `b_{h, i} ↦ 0` for `i < k`).

    SOUNDNESS DIRECTION: justified by the fact that the low k bits
    of `(2^k * x) mod 2^d` are always zero (independent of x).

    Proof. `h.val = (2^k * x.val) mod 2^d`. By Nat.testBit_mod_two_pow
    and Nat.testBit_mul_pow_two:
      ((2^k * x.val) mod 2^d).testBit i
        = (decide (i < d) && decide (k ≤ i) && testBit x.val (i - k))
    For i < k, `decide (k ≤ i) = false`, so the whole expression is
    `false`. -/
theorem scalar_alignment_low_bits_zero {d k : ℕ} (_hd : 0 < d) (hk : k < d)
    (x : ZMod (2 ^ d)) (h : ZMod (2 ^ d))
    (heq : h = (2 ^ k : ZMod (2 ^ d)) * x) :
    ∀ i, i < k → Re4.stdBit d i h = 0 := by
  intro i hik
  unfold Re4.stdBit
  have h_val : h.val = (2 ^ k * x.val) % 2 ^ d := by
    rw [heq, ZMod.val_mul, val_two_pow_lt hk]
  have h_no : Nat.testBit h.val i = false := by
    rw [h_val, Nat.testBit_mod_two_pow, Nat.testBit_mul_pow_two]
    have h_not_le : ¬ (k ≤ i) := by omega
    simp [h_not_le]
  simp [h_no]

/-! ## (2) Shifted bit alignment

    For h = 2^k * x mod 2^d, bit i+k of h equals bit i of x when
    i + k < d (i.e., the shifted bit doesn't overflow).
-/

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::materialise_bit_alignments
    (the shift-alignment substitutions:
     `b_{h, i+k} ↦ b_{x, i}` for `0 ≤ i < d-k`).

    SOUNDNESS DIRECTION: justified by the standard binary expansion:
    bit i+k of `(2^k * x) mod 2^d` equals bit i of `x mod 2^(d-k)`
    which equals bit i of x (since i < d-k ≤ d).

    Proof. `h.val = (2^k * x.val) mod 2^d`. By Nat.testBit_mod_two_pow
    and Nat.testBit_mul_pow_two, the bit at position `i+k` is:
      decide (i + k < d) && decide (k ≤ i + k) && testBit x.val ((i+k) - k)
    With `i + k < d` and `k ≤ i + k` both true, and `(i+k) - k = i`,
    this simplifies to `testBit x.val i`. -/
theorem scalar_alignment_shifted_bits {d k : ℕ} (_hd : 0 < d) (hk : k < d)
    (x : ZMod (2 ^ d)) (h : ZMod (2 ^ d))
    (heq : h = (2 ^ k : ZMod (2 ^ d)) * x) :
    ∀ i, i + k < d → Re4.stdBit d (i + k) h = Re4.stdBit d i x := by
  intro i hik
  unfold Re4.stdBit
  have h_val : h.val = (2 ^ k * x.val) % 2 ^ d := by
    rw [heq, ZMod.val_mul, val_two_pow_lt hk]
  have h_eq_bit : Nat.testBit h.val (i + k) = Nat.testBit x.val i := by
    rw [h_val, Nat.testBit_mod_two_pow, Nat.testBit_mul_pow_two]
    have h1 : i + k < d := hik
    have h2 : k ≤ i + k := Nat.le_add_left _ _
    have h3 : (i + k) - k = i := Nat.add_sub_cancel _ _
    simp [h1, h2, h3]
  rw [h_eq_bit]

/-- Combined: the alignment substitutions registered by
    `materialise_bit_alignments` are valid consequences in the
    bit-decomposed model of any polynomial system that contains
    `h - 2^k * x = 0`. -/
theorem scalar_alignment_consequence {d k : ℕ} (hd : 0 < d) (hk : k < d)
    (x h : ZMod (2 ^ d)) (heq : h = (2 ^ k : ZMod (2 ^ d)) * x) :
    (∀ i, i < k → Re4.stdBit d i h = 0) ∧
    (∀ i, i + k < d → Re4.stdBit d (i + k) h = Re4.stdBit d i x) :=
  ⟨scalar_alignment_low_bits_zero hd hk x h heq,
   scalar_alignment_shifted_bits hd hk x h heq⟩

end BitAlignment
