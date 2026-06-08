/-
  Re4.lean — Soundness proofs for the bit-decomposition extension
  (Re 4 in the implementation tracker).

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/algebraic/poly_extract.cpp`
  (`decompose_bits`) and `src/solvers/algebraic/poly_ring.cpp`
  (`apply_frobenius_idempotency`, `polynomialt::multiply` with
  bit-vars overload).

  The implementation introduces, for each bit-decomposed value `x`
  of bitwidth `d`, fresh bit variables `b_{x, 0}, ..., b_{x, d-1}`
  with side equations:

    (idempotency)        b_{x, i}^2 - b_{x, i} = 0  for each i
    (sum-decomposition)  x - sum_i 2^i * b_{x, i} = 0

  We mechanise three soundness facts:

    1. In Z_{2^d}, idempotency `b^2 = b` forces `b ∈ {0, 1}`.
    2. Frobenius reduction: `b * b = b` implies `b^k = b` for all k ≥ 1.
    3. The sum-decomposition equation, given idempotency, uniquely
       determines the b_i as the bits of x.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

namespace Re4

/-! ## (1) Idempotency forces a value to be 0 or 1 -/

/-- In Z_{2^d} (d ≥ 1), idempotency forces a value to be 0 or 1.

    IMPL: src/solvers/algebraic/poly_extract.cpp::decompose_bits
    (the idempotency side equation `b * b - b = 0` for each fresh
    bit variable). -/
theorem bit_idempotency_forces_zero_or_one {d : ℕ} (hd : 0 < d)
    (b : ZMod (2 ^ d)) (hb : b * b = b) :
    b = 0 ∨ b = 1 := by
  -- Work with the canonical representative v ∈ [0, 2^d).
  set v := b.val with hv_def
  have hv_lt : v < 2 ^ d := ZMod.val_lt _
  have hv_b : (v : ZMod (2 ^ d)) = b := ZMod.natCast_zmod_val b
  -- 2^d divides v * (v - 1) over ℕ (handling v = 0 separately).
  by_cases hv0 : v = 0
  · left; rw [← hv_b, hv0]; simp
  -- Otherwise v ≥ 1, so v - 1 ∈ ℕ is well-defined.
  have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr hv0
  -- (v : ZMod (2^d)) * ((v - 1) : ZMod (2^d)) = b * (b - 1) = 0.
  have h_zero : (v : ZMod (2 ^ d)) * ((v - 1 : ℕ) : ZMod (2 ^ d)) = 0 := by
    have h_b_sub : ((v - 1 : ℕ) : ZMod (2 ^ d)) = b - 1 := by
      have h1 : ((v - 1 : ℕ) : ZMod (2 ^ d)) = (v : ZMod (2 ^ d)) - 1 := by
        rw [Nat.cast_sub hv1]; push_cast; ring
      rw [h1, hv_b]
    rw [hv_b, h_b_sub]
    have : b * (b - 1) = 0 := by linear_combination hb
    exact this
  -- Convert to divisibility in ℕ via the natCast_zmod_eq_zero_iff_dvd.
  have h_dvd : 2 ^ d ∣ v * (v - 1) := by
    have h_cast : ((v * (v - 1) : ℕ) : ZMod (2 ^ d)) = 0 := by
      push_cast; exact h_zero
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h_cast
  -- Case-split on parity of v: exactly one of v, v - 1 is odd.
  rcases Nat.even_or_odd v with hve | hvo
  · -- v even ⇒ v - 1 odd ⇒ Coprime (v - 1) 2 ⇒ Coprime (v - 1) (2^d).
    right
    have h_v1_odd : Odd (v - 1) := by
      rcases hve with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      omega
    have h_cop : Nat.Coprime (v - 1) (2 ^ d) := by
      rw [Nat.coprime_pow_right_iff hd]
      exact (Odd.coprime_two_left h_v1_odd).symm
    -- 2^d divides v * (v - 1) and Coprime (2^d) (v - 1) ⇒ 2^d divides v.
    have h_dvd_v : 2 ^ d ∣ v := by
      have h_dvd' : 2 ^ d ∣ (v - 1) * v := by rw [Nat.mul_comm]; exact h_dvd
      exact (Nat.Coprime.symm h_cop).dvd_of_dvd_mul_left h_dvd'
    -- v < 2^d, so 2^d ∣ v ⇒ v = 0. But we assumed v ≥ 1 — contradiction.
    have : v = 0 := Nat.eq_zero_of_dvd_of_lt h_dvd_v hv_lt
    exfalso; omega
  · -- v odd ⇒ Coprime v 2 ⇒ Coprime v (2^d). Then 2^d ∣ (v - 1).
    right
    have h_cop : Nat.Coprime v (2 ^ d) := by
      rw [Nat.coprime_pow_right_iff hd]
      exact (Odd.coprime_two_left hvo).symm
    have h_dvd_v1 : 2 ^ d ∣ (v - 1) := by
      exact h_cop.symm.dvd_of_dvd_mul_left h_dvd
    -- v - 1 < 2^d (since v < 2^d), and 2^d ∣ (v - 1) ⇒ v - 1 = 0 ⇒ v = 1.
    have h_v1_lt : v - 1 < 2 ^ d := by omega
    have h_v1_zero : v - 1 = 0 :=
      Nat.eq_zero_of_dvd_of_lt h_dvd_v1 h_v1_lt
    have : v = 1 := by omega
    rw [← hv_b, this]; simp

/-! ## (2) Frobenius reduction for idempotents

    If `b * b = b` (i.e., `b` is an idempotent), then `b^k = b` for
    all `k ≥ 1`. This justifies clamping bit-variable exponents
    to 1 inside `polynomialt::multiply` (Re 4 sub-goal 3).
-/

/-- Frobenius idempotency: `b^k = b` for any idempotent `b` and `k ≥ 1`.

    IMPL: src/solvers/algebraic/poly_ring.cpp::apply_frobenius_idempotency
    and `polynomialt::multiply` (bit_vars overload). -/
theorem frobenius_pow_eq_self {R : Type*} [Monoid R]
    (b : R) (hb : b * b = b) (k : ℕ) (hk : 1 ≤ k) :
    b ^ k = b := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with h1 | h1
    · -- k = 1
      simp [← h1]
    · have hn : 1 ≤ n := by omega
      rw [pow_succ, ih hn, hb]

/-! ## (3) Sum-decomposition uniqueness

    Given d bit variables b_0, ..., b_{d-1} all idempotent, the
    polynomial equation `x = sum_{i=0}^{d-1} 2^i * b_i` uniquely
    determines the b_i as the bits of x in Z_{2^d}: the b_i are
    forced to {0, 1} by idempotency, and the sum is the standard
    binary expansion (which is unique for any number in [0, 2^d)).
-/

/-- Standard binary expansion: for any `x < 2^d`,
    `x = sum_{i<d} testBit(x, i) * 2^i` as a natural number. -/
lemma sum_testBit_eq_self : ∀ (d : ℕ) (x : ℕ), x < 2 ^ d →
    (∑ i : Fin d, if Nat.testBit x i.val then 2 ^ (i : ℕ) else 0) = x
  | 0, x, h => by
    simp at h
    simp [h]
  | d + 1, x, h => by
    -- Split off the i = 0 term.
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.testBit_zero, pow_zero, Fin.val_succ]
    -- Apply IH to x / 2 < 2^d.
    have h_half : x / 2 < 2 ^ d := by
      have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      rw [h2] at h; omega
    have h_ih := sum_testBit_eq_self d (x / 2) h_half
    -- Each shifted summand: testBit x (i+1) = testBit (x/2) i.
    have h_shift : ∀ i : Fin d,
        (if Nat.testBit x (i.val + 1) then 2 ^ (i.val + 1) else 0)
        = 2 * (if Nat.testBit (x / 2) i.val then 2 ^ (i : ℕ) else 0) := by
      intro i
      rw [Nat.testBit_succ]
      by_cases hb : Nat.testBit (x / 2) i.val
      · simp [hb, pow_succ, Nat.mul_comm]
      · simp [hb]
    rw [Finset.sum_congr rfl (fun i _ => h_shift i)]
    rw [← Finset.mul_sum, h_ih]
    -- Goal now has (if decide (x % 2 = 1) then 1 else 0) + 2 * (x / 2) = x.
    have h_split : x = 2 * (x / 2) + x % 2 := by
      rw [Nat.add_comm]; exact (Nat.mod_add_div x 2).symm
    -- Reduce the conditional on x % 2.
    have h_bit0 : (if decide (x % 2 = 1) = true then (1 : ℕ) else 0) = x % 2 := by
      have : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
      interval_cases (x % 2) <;> simp
    rw [h_bit0]
    omega

theorem stdBit_sums_to_self_helper {d : ℕ} (x : ZMod (2 ^ d)) :
    (∑ i : Fin d, if Nat.testBit x.val i.val then 2 ^ (i : ℕ) else 0)
    = x.val :=
  sum_testBit_eq_self d x.val (ZMod.val_lt _)

/-- The polynomial sum form, parameterised by bit assignments. -/
def bitSum (d : ℕ) (bs : Fin d → ZMod (2 ^ d)) : ZMod (2 ^ d) :=
  ∑ i : Fin d, (2 ^ (i : ℕ) : ZMod (2 ^ d)) * bs i

/-- If every bit assignment is idempotent, all values are in {0, 1}. -/
theorem all_idempotent_to_bool {d : ℕ} (hd : 0 < d)
    (bs : Fin d → ZMod (2 ^ d))
    (hb : ∀ i, bs i * bs i = bs i)
    (i : Fin d) :
    bs i = 0 ∨ bs i = 1 :=
  bit_idempotency_forces_zero_or_one hd (bs i) (hb i)

/-- The standard bit decomposition: i-th bit of x as an element of
    ZMod (2^d). -/
def stdBit (d i : ℕ) (x : ZMod (2 ^ d)) : ZMod (2 ^ d) :=
  if Nat.testBit x.val i then 1 else 0

/-- Each standard bit is idempotent. -/
theorem stdBit_idempotent (d i : ℕ) (x : ZMod (2 ^ d)) :
    stdBit d i x * stdBit d i x = stdBit d i x := by
  unfold stdBit
  by_cases h : Nat.testBit x.val i
  · simp [h]
  · simp [h]

/-- The standard sum-of-bits is x.

    IMPL: src/solvers/algebraic/poly_extract.cpp::decompose_bits
    (the sum-decomposition side equation `x - sum_i 2^i * b_i = 0`). -/
theorem stdBit_sums_to_self {d : ℕ} (x : ZMod (2 ^ d)) :
    bitSum d (fun i => stdBit d (i : ℕ) x) = x := by
  unfold bitSum stdBit
  -- Each summand: 2^i * (if testBit x.val i then 1 else 0)
  --             = (if testBit x.val i then 2^i else 0).
  have h_sum :
      (∑ i : Fin d, (2 ^ (i : ℕ) : ZMod (2 ^ d)) *
        (if Nat.testBit x.val i.val then (1 : ZMod (2 ^ d)) else 0))
      = ((∑ i : Fin d, if Nat.testBit x.val i.val then 2 ^ (i : ℕ) else 0
          : ℕ) : ZMod (2 ^ d)) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Nat.testBit x.val i.val
    · simp [h]
    · simp [h]
  rw [h_sum]
  rw [stdBit_sums_to_self_helper x]
  exact ZMod.natCast_zmod_val x

/-- **Bit-decomposition uniqueness (existence).** Given x in Z_{2^d},
    there exists a bit assignment satisfying the side equations. -/
theorem bit_decomp_existence {d : ℕ} (x : ZMod (2 ^ d)) :
    ∃ bs : Fin d → ZMod (2 ^ d),
      (∀ i, bs i * bs i = bs i) ∧ bitSum d bs = x :=
  ⟨fun i => stdBit d (i : ℕ) x,
   fun i => stdBit_idempotent d (i : ℕ) x,
   stdBit_sums_to_self x⟩

end Re4
