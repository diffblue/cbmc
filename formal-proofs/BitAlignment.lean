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

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::materialise_bit_alignments
    (the low-bit-zero substitutions: `b_{h, i} ↦ 0` for `i < k`).

    SOUNDNESS DIRECTION: justified by the fact that the low k bits
    of `(2^k * x) mod 2^d` are always zero (independent of x).

    PROOF STATUS: statement complete; mechanised proof admitted as
    `sorry` for now. Informal argument: the natural-number
    representation of `(2^k * x) mod 2^d` has its low k bits as 0
    because multiplication by 2^k shifts the bits of `x mod 2^(d-k)`
    up by k, leaving the low k positions zero. -/
theorem scalar_alignment_low_bits_zero {d k : ℕ} (hd : 0 < d) (hk : k < d)
    (x : ZMod (2 ^ d)) (h : ZMod (2 ^ d))
    (heq : h = (2 ^ k : ZMod (2 ^ d)) * x) :
    ∀ i, i < k → Re4.stdBit d i h = 0 := by
  sorry

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

    PROOF STATUS: statement complete; mechanised proof admitted as
    `sorry` for now. Informal argument: as above. -/
theorem scalar_alignment_shifted_bits {d k : ℕ} (hd : 0 < d) (hk : k < d)
    (x : ZMod (2 ^ d)) (h : ZMod (2 ^ d))
    (heq : h = (2 ^ k : ZMod (2 ^ d)) * x) :
    ∀ i, i + k < d → Re4.stdBit d (i + k) h = Re4.stdBit d i x := by
  sorry

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
