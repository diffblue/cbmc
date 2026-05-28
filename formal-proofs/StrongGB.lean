/-
  StrongGB.lean — Soundness and completeness of the strong Gröbner
  basis 2-trick saturation in Z_{2^d}.

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/algebraic/groebner.cpp`
  (`compute`, the 2-multiple step in particular).

  ## Overview

  This module captures the soundness and the completeness situation
  of the strong-GB algorithm with 2-trick saturation as used in
  `src/solvers/algebraic/groebner.cpp::compute`.

  Soundness (DONE, no sorry):

    1. (`two_trick_preserves_ideal`, `two_trick_preserves_ideal_mv`)
       Scalar multiplication preserves ideal membership; this
       justifies the 2-trick saturation step.

    2. (`two_trick_unsat_sound`) An odd constant in the basis
       implies the original ideal is the whole ring, i.e., UNSAT.
       Re-exported from `GroebnerSoundness.lean`.

  Completeness situation (RESEARCH-LEVEL):

  ## Important finding: the naive completeness statement is FALSE.

  In an earlier draft of this module we stated:

      For F unsatisfiable on `(ZMod (2^d))^n`, the strong-GB
      algorithm produces a basis containing an odd constant.

  This is **false** without further hypotheses. The
  `naive_completeness_is_false` theorem below proves it with a
  concrete counterexample (`d = 2`, `n = 0`, `F = {C 2}`):

    - `F` is unsatisfiable (the constant `2 ≠ 0` in `ZMod 4`).
    - `Ideal.span F` does not contain any odd constant (the ideal
      is `(2) ⊆ ZMod 4 = {0, 2}`, which excludes the odd
      elements `1, 3`).

  Adding bit-variable idempotency does not fix the issue: e.g.,
  `F = {C 2, b^2 - b}` over `MvPolynomial (Fin 1) (ZMod 4)` has
  the same problem (every element of `Ideal.span F` has even
  constant term).

  ## What Song et al. actually prove

  Song et al. (TACAS 2024) prove a more careful completeness
  theorem: not for arbitrary polynomial systems, but for **the
  specific polynomial-system encoding of a bit-vector formula**
  produced by their (and our) translation. Their encoding has
  additional structure beyond idempotency:

    - All polynomials arise from translating equational
      bit-vector predicates.
    - Coefficients have a 2-adic structure tied to the bit
      positions.
    - The combinatorial structure of the polynomials interacts
      well with the 2-trick saturation rule.

  Without that structure, even unsatisfiable systems can have
  ideals that don't contain a unit.

  Mechanising the actual Song et al. theorem requires:

    (a) A formal definition of the bit-vector formula -> polynomial-
        system encoding.
    (b) The five-step mechanisation outlined in the
        `two_trick_saturation_complete` docstring (extended
        division algorithm, 2-trick step, termination,
        soundness, completeness).
    (c) The deep completeness step itself: a constructive proof
        that the strong-GB algorithm finds an odd constant when
        the encoding is unsatisfiable.

  This is a substantial research project. We provide:

    - A precise statement of the naive (false) version with a
      counterexample.
    - A precise statement of a refined version with strengthened
      hypotheses (the implementation's encoding structure),
      admitted as `sorry`.
    - Several mathlib-contributable lemmas about `ZMod (2^d)`
      that are used in the proof.

  ## Mathlib-contributable lemmas

  These results about `ZMod (2^d)` are general-purpose and
  not specific to the strong-GB context:

    - `IsLocalRing (ZMod (p^n))` for prime p (omitted for now;
      candidate contribution).

    - `ZMod.isUnit_iff_two_not_dvd_val` (specialised from
      `ZMod.isUnit_iff_coprime`).

  See the `MathlibCandidates` namespace below.
-/

import GroebnerSoundness
import BuchbergerCorrectness
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

namespace StrongGB

/-! ## (1) 2-trick preserves the ideal -/

/-- IMPL: src/solvers/algebraic/groebner.cpp::compute
    (the 2-multiple step: doubles selected polynomials with the
    appropriate scalar multiplier).

    SOUNDNESS DIRECTION: scalar multiplication preserves ideal
    membership, which is `Ideal.mul_mem_right`. -/
theorem two_trick_preserves_ideal {d : ℕ} (I : Ideal (ZMod (2 ^ d)))
    {f : ZMod (2 ^ d)} (hf : f ∈ I) (k : ℕ) :
    f * (2 ^ k : ZMod (2 ^ d)) ∈ I :=
  I.mul_mem_right _ hf

/-- The same fact lifted to `MvPolynomial (Fin n) (ZMod (2^d))`. -/
theorem two_trick_preserves_ideal_mv {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) (ZMod (2 ^ d))))
    {f : MvPolynomial (Fin n) (ZMod (2 ^ d))} (hf : f ∈ I) (k : ℕ) :
    f * (MvPolynomial.C (2 ^ k : ZMod (2 ^ d))) ∈ I :=
  I.mul_mem_right _ hf

/-! ## (2) 2-trick is sound for UNSAT detection -/

/-- IMPL: src/solvers/algebraic/groebner.cpp::compute
    (when the basis contains an odd constant, the procedure reports
    UNSAT).

    SOUNDNESS DIRECTION: the existing `soundness_of_odd_constant_check`
    in `GroebnerSoundness.lean` already proves this. We re-export
    here for completeness. -/
theorem two_trick_unsat_sound {d : ℕ}
    (I : Ideal (ZMod (2 ^ d))) {c : ℕ} (hc_odd : ¬ 2 ∣ c)
    (hc_mem : (c : ZMod (2 ^ d)) ∈ I) :
    I = ⊤ :=
  soundness_of_odd_constant_check I hc_odd hc_mem

/-! ## (3) The naive completeness statement is FALSE

    We show that the statement "F unsatisfiable on `(ZMod (2^d))^n`
    implies the ideal of F contains an odd constant" is false.
    This explains why the implementation's algorithm CAN return
    UNKNOWN even on unsatisfiable inputs (see `groebner.h`'s
    `resultt::UNKNOWN`): the polynomial system might genuinely
    encode an unsatisfiable problem whose ideal doesn't contain a
    unit.

    Counterexample: `d = 2`, `n = 0`, `F = {MvPolynomial.C 2}`.
-/

/-- Helper: in `ZMod 4`, an odd constant `c` is not in the ideal
    `Ideal.span {2}`.

    This is essentially `Ideal.mem_span_singleton` plus the fact
    that `2 ∤ c` in `ℕ` implies `(2 : ZMod 4) ∤ (c : ZMod 4)`. -/
lemma odd_not_in_two_ideal_zmod_four {c : ℕ} (hc : ¬ 2 ∣ c) :
    ¬ (c : ZMod 4) ∈ Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)) := by
  rw [Ideal.mem_span_singleton]
  -- Goal: ¬ (2 ∣ (c : ZMod 4)).
  -- Reason: (c : ZMod 4) ∈ {1, 3} for odd c, and 2 ∣ x in ZMod 4
  -- means x ∈ {0, 2}.
  intro h_dvd
  -- `c mod 4` is 1 or 3 (since c is odd).
  have h_c_mod : c % 4 = 1 ∨ c % 4 = 3 := by omega
  -- The image (c : ZMod 4) is determined by c mod 4.
  have h_in_odd : (c : ZMod 4) = 1 ∨ (c : ZMod 4) = 3 := by
    rcases h_c_mod with h | h
    · left
      have h_val : (c : ZMod 4).val = 1 := by
        rw [ZMod.val_natCast]; exact h
      have h_eq_one_cast : (c : ZMod 4) = ((1 : ℕ) : ZMod 4) := by
        rw [← ZMod.natCast_zmod_val (c : ZMod 4), h_val]
      simpa using h_eq_one_cast
    · right
      have h_val : (c : ZMod 4).val = 3 := by
        rw [ZMod.val_natCast]; exact h
      have h_eq_three_cast : (c : ZMod 4) = ((3 : ℕ) : ZMod 4) := by
        rw [← ZMod.natCast_zmod_val (c : ZMod 4), h_val]
      simpa using h_eq_three_cast
  -- For x ∈ {1, 3} in ZMod 4, ¬ (2 ∣ x). Concretely:
  -- if 2 ∣ 1 in ZMod 4: 1 = 2 * k for some k. Check k ∈ {0, 1, 2, 3}:
  -- 2*0=0, 2*1=2, 2*2=0, 2*3=2. None equal 1. Contradiction.
  -- Similarly for 3.
  rcases h_in_odd with h | h
  · -- (c : ZMod 4) = 1, h_dvd : 2 ∣ 1.
    rw [h] at h_dvd
    -- 2 ∣ 1 in ZMod 4 is decidable; explicitly false.
    have : ¬ ((2 : ZMod 4) ∣ 1) := by
      intro ⟨k, hk⟩
      revert hk
      fin_cases k <;> decide
    exact this h_dvd
  · -- (c : ZMod 4) = 3, h_dvd : 2 ∣ 3.
    rw [h] at h_dvd
    have : ¬ ((2 : ZMod 4) ∣ 3) := by
      intro ⟨k, hk⟩
      revert hk
      fin_cases k <;> decide
    exact this h_dvd

/-- The naive completeness statement is false.

    Concretely: there exist `d, n, F` with `F` unsatisfiable on
    `(ZMod (2^d))^n` such that `Ideal.span F` contains no odd
    constant.

    The counterexample is `d = 2`, `n = 0`, `F = {C 2}` over
    `MvPolynomial (Fin 0) (ZMod 4)`. The ideal is `(C 2)` which
    corresponds to `(2) ⊆ ZMod 4 = {0, 2}`, excluding the odd
    constants `1, 3`.

    This shows that `two_trick_saturation_complete`, as it might
    be naively stated, is FALSE. The actual Song et al. theorem
    requires F to have specific structure (the bit-vector
    encoding) that excludes such trivial counterexamples. -/
theorem naive_completeness_is_false :
    ∃ (d n : ℕ) (_hd : 0 < d) (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d)))),
      (∀ φ : Fin n → ZMod (2 ^ d),
         ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0) ∧
      ¬ ∃ (c : ℕ), ¬ 2 ∣ c ∧
        (MvPolynomial.C (c : ZMod (2 ^ d))
          : MvPolynomial (Fin n) (ZMod (2 ^ d)))
          ∈ Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) F := by
  refine ⟨2, 0, by norm_num,
          ({MvPolynomial.C 2} : Finset (MvPolynomial (Fin 0) (ZMod 4))),
          ?_, ?_⟩
  · -- F unsat: every assignment makes some polynomial nonzero.
    intro φ
    refine ⟨MvPolynomial.C 2, ?_, ?_⟩
    · simp
    · -- MvPolynomial.eval φ (C 2) = 2 ≠ 0 in ZMod 4.
      simp only [MvPolynomial.eval_C]
      decide
  · -- No odd constant in `Ideal.span {C 2}`.
    rintro ⟨c, hc_odd, hc_mem⟩
    -- Use the ring iso to reduce to ZMod 4.
    -- MvPolynomial (Fin 0) (ZMod 4) ≅ ZMod 4 via isEmptyRingEquiv.
    -- Under this iso, C r maps to r and Ideal.span {C 2} maps to
    -- Ideal.span {2}. Then odd_not_in_two_ideal_zmod_four applies.
    let φ := MvPolynomial.isEmptyRingEquiv (ZMod 4) (Fin 0)
    have h_F_eq : (({MvPolynomial.C 2} : Finset (MvPolynomial (Fin 0) (ZMod 4)))
                   : Set _)
                = ({MvPolynomial.C 2} : Set (MvPolynomial (Fin 0) (ZMod 4))) := by
      simp
    rw [h_F_eq] at hc_mem
    -- Apply the iso: ideal span containment is preserved.
    -- The image of `C c` under φ is c, image of `Ideal.span {C 2}` is `Ideal.span {2}`.
    have h_phi_C : ∀ r : ZMod 4, φ (MvPolynomial.C r) = r := by
      intro r
      show (MvPolynomial.isEmptyAlgEquiv (ZMod 4) (Fin 0)) (MvPolynomial.C r) = r
      simp [MvPolynomial.isEmptyAlgEquiv]
    -- We have: C c ∈ Ideal.span {C 2}.
    -- Apply φ: c = φ(C c) ∈ φ(Ideal.span {C 2}) = Ideal.span {2}.
    have h_image : (c : ZMod 4) ∈ Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)) := by
      rw [show ((c : ZMod 4) : ZMod 4) = φ (MvPolynomial.C (c : ZMod 4)) from
          (h_phi_C _).symm]
      have h_2_eq : (2 : ZMod 4) = φ (MvPolynomial.C 2) := (h_phi_C _).symm
      rw [h_2_eq]
      -- φ is a ring iso; it maps Ideal.span {C 2} to Ideal.span {φ(C 2)}.
      have : Ideal.map φ.toRingHom
              (Ideal.span ({MvPolynomial.C 2} : Set (MvPolynomial (Fin 0) (ZMod 4))))
            = Ideal.span ({φ (MvPolynomial.C 2)} : Set (ZMod 4)) := by
        rw [Ideal.map_span]
        simp
      rw [this.symm]
      exact Ideal.mem_map_of_mem φ.toRingHom hc_mem
    exact odd_not_in_two_ideal_zmod_four hc_odd h_image

/-! ## (4) The actual Song et al. completeness theorem

    The corrected statement requires F to have the structure of
    the bit-vector encoding: idempotency for each variable + the
    polynomials arising from the BV-formula translation.

    We state this theorem precisely, modulo a placeholder for
    "F is the encoding of a BV formula", and admit the proof.

    A full formalisation would:
      (i)  Define `BVFormula` and the encoding function
           `encode : BVFormula -> Finset (MvPolynomial _ (ZMod (2^d)))`.
      (ii) State the theorem in terms of `encode`.
      (iii) Prove the theorem using Song et al.'s argument.

    Items (i)–(iii) collectively constitute the full Song et al.
    mechanisation, comparable to a master's thesis.
-/

/-- Predicate: F is "well-formed" in the sense of arising from
    the bit-vector encoding. Concretely (placeholder definition):
    F includes idempotency for each variable. The full predicate
    in Song et al. is stronger; we use a placeholder here. -/
def WellFormedEncoding {n d : ℕ}
    (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d)))) : Prop :=
  ∀ i : Fin n, MvPolynomial.X i ^ 2 - MvPolynomial.X i ∈ F

/-- The strong-GB algorithm: given a finite polynomial set `F`
    over `MvPolynomial (Fin n) (ZMod (2^d))`, returns the strong
    Gröbner basis. Declared axiomatically here to match the
    implementation in `groebner.cpp::compute`. -/
axiom strongGB {n d : ℕ} :
    Finset (MvPolynomial (Fin n) (ZMod (2 ^ d))) →
    Finset (MvPolynomial (Fin n) (ZMod (2 ^ d)))

/-- Soundness axiom: strongGB preserves the ideal generated. -/
axiom strongGB_ideal_preserved {n d : ℕ}
    (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d)))) :
    Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) (strongGB F)
    = Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) F

/-- Refined completeness: for `F` arising from the bit-vector
    encoding (a stronger hypothesis than just "F unsatisfiable
    over `(ZMod (2^d))^n`"), the strong-GB algorithm produces a
    basis containing an odd constant.

    PROOF STATUS: STATEMENT-ONLY. The proof is the Song et al.
    (TACAS 2024) theorem. See module docstring for the
    decomposition required to mechanise it. The
    `WellFormedEncoding` placeholder needs to be replaced with
    the full structural predicate from the BV-encoding (which
    requires a formal definition of bit-vector formulas and
    their encoding into polynomial systems).

    The naive version without `hwf` is FALSE; see
    `naive_completeness_is_false` above. -/
theorem two_trick_saturation_complete {n d : ℕ} (hd : 0 < d)
    (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d))))
    (hwf : WellFormedEncoding F)
    (hunsat : ∀ φ : Fin n → ZMod (2 ^ d),
              ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0) :
    ∃ c : ℕ, ¬ 2 ∣ c ∧
      (MvPolynomial.C (c : ZMod (2 ^ d))
        : MvPolynomial (Fin n) (ZMod (2 ^ d))) ∈ strongGB F := by
  sorry

/-! ## (5) Mathlib-contributable lemmas

    Lemmas in this section are general-purpose facts about
    `ZMod (2^d)` that are not specific to the strong-GB context
    and are candidates for mathlib contribution.
-/

namespace MathlibCandidates

/-- An odd natural number is a unit in `ZMod (2^d)`.

    This is a specialisation of `ZMod.isUnit_iff_coprime`. The
    coprimality condition `Coprime c (2^d)` is equivalent to
    `¬ 2 ∣ c` (via `Nat.Coprime.pow_right_iff`).

    MATHLIB CANDIDATE. This is essentially `ZMod.isUnit_of_odd_nat`
    in `formal-proofs/GroebnerSoundness.lean` already; here it
    serves as a label for mathlib contribution. -/
theorem isUnit_of_odd_nat_in_two_pow {d : ℕ} {c : ℕ} (hc : ¬ 2 ∣ c) :
    IsUnit (c : ZMod (2 ^ d)) :=
  ZMod.isUnit_of_odd_nat hc

/-- An element of `ZMod (2^d)` is a unit iff its lift to `ℕ` is
    odd (not divisible by 2).

    MATHLIB CANDIDATE. The forward direction is direct from
    `ZMod.isUnit_iff_coprime`; the reverse is
    `isUnit_of_odd_nat_in_two_pow`. -/
theorem isUnit_iff_two_not_dvd_val {d : ℕ} (hd : 0 < d) (x : ZMod (2 ^ d)) :
    IsUnit x ↔ ¬ 2 ∣ x.val := by
  constructor
  · intro h_unit
    have h_coprime : Nat.Coprime x.val (2 ^ d) := by
      have := (ZMod.isUnit_iff_coprime x.val (2 ^ d)).mp
      have h_cast : (x.val : ZMod (2 ^ d)) = x := ZMod.natCast_zmod_val x
      rw [← h_cast] at h_unit
      exact this h_unit
    intro h_two_dvd
    have h_two_dvd_pow : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega : d ≠ 0)
    have h_two_dvd_gcd : 2 ∣ Nat.gcd x.val (2 ^ d) :=
      Nat.dvd_gcd h_two_dvd h_two_dvd_pow
    rw [Nat.coprime_iff_gcd_eq_one.mp h_coprime] at h_two_dvd_gcd
    omega
  · intro h_odd
    have h_x_eq : (x.val : ZMod (2 ^ d)) = x := ZMod.natCast_zmod_val x
    rw [← h_x_eq]
    exact ZMod.isUnit_of_odd_nat h_odd

end MathlibCandidates

/-! ## (6) IsLocalRing (ZMod (p^n)) — mathlib contribution candidate

    The ring `ZMod (p^n)` for prime `p` and `n ≥ 1` is a local ring.
    The unique maximal ideal is `(p)`. Equivalently: for any
    `a : ZMod (p^n)`, either `a` is a unit (coprime to `p^n`) or
    `1 - a` is a unit.

    Proof: if `a + b = 1` and neither is a unit, then `p | a.val`
    and `p | b.val` (since non-units in `ZMod (p^n)` are exactly
    the multiples of `p`). But then `p | (a.val + b.val) % p^n = 1`,
    contradicting `p ≥ 2`.

    This is NOT currently in mathlib (verified by grep). It is a
    clean, self-contained instance suitable for contribution.
-/

namespace MathlibCandidates

/-- In `ZMod (p^n)` for prime `p`, a non-unit has `p | val`. -/
private lemma not_isUnit_iff_prime_dvd_val {p n : ℕ} (hp : Nat.Prime p) (_hn : 0 < n)
    [NeZero (p ^ n)] (x : ZMod (p ^ n)) :
    ¬ IsUnit x → p ∣ x.val := by
  intro h_not_unit
  -- Contrapositive: if ¬ (p | x.val) then x is a unit.
  by_contra h_not_dvd
  apply h_not_unit
  -- ¬ (p | x.val) means x.val is coprime to p^n (since p is the only prime factor of p^n)
  have h_coprime : Nat.Coprime x.val (p ^ n) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_gcd
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h_gcd
    have hq_dvd_x : q ∣ x.val := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
    have hq_dvd_pn : q ∣ p ^ n := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
    have hq_eq_p : q = p :=
      (hp.eq_one_or_self_of_dvd q (hq_prime.dvd_of_dvd_pow hq_dvd_pn)).resolve_left
        hq_prime.one_lt.ne'
    exact h_not_dvd (hq_eq_p ▸ hq_dvd_x)
  have h_cast : (x.val : ZMod (p ^ n)) = x := ZMod.natCast_zmod_val x
  rw [← h_cast]
  exact (ZMod.isUnit_iff_coprime x.val (p ^ n)).mpr h_coprime

/-- `ZMod (p^n)` is a local ring for prime `p` and `n ≥ 1`.

    MATHLIB CANDIDATE. The unique maximal ideal is `(p)`.
    An element is a unit iff it is coprime to `p^n`, i.e., iff
    `p` does not divide its representative. -/
instance isLocalRing_ZMod_prime_pow {p : ℕ} (hp : Nat.Prime p) (n : ℕ) (hn : 0 < n) :
    IsLocalRing (ZMod (p ^ n)) := by
  haveI h_lt : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
  haveI : NeZero (p ^ n) := ⟨by
    have := h_lt.1
    omega⟩
  exact {
    exists_pair_ne := ⟨0, 1, by
      intro h
      have : (0 : ZMod (p ^ n)).val = (1 : ZMod (p ^ n)).val := congrArg ZMod.val h
      simp [ZMod.val_one] at this⟩
    isUnit_or_isUnit_of_add_one := by
      intro a b hab
      -- Either p ∤ a.val (so a is a unit) or p ∤ b.val (so b is a unit).
      by_contra h_neither
      push_neg at h_neither
      obtain ⟨ha, hb⟩ := h_neither
      have ha_dvd : p ∣ a.val := not_isUnit_iff_prime_dvd_val hp hn a ha
      have hb_dvd : p ∣ b.val := not_isUnit_iff_prime_dvd_val hp hn b hb
      -- From a + b = 1: (a.val + b.val) % p^n = 1
      have h_one_val : (1 : ZMod (p ^ n)).val = 1 := ZMod.val_one (p ^ n)
      have h_sum_val : (a + b).val = (a.val + b.val) % (p ^ n) := ZMod.val_add a b
      rw [hab] at h_sum_val
      -- So 1 = (a.val + b.val) % p^n, and p | a.val + b.val, so p | 1.
      have h_p_dvd_sum : p ∣ a.val + b.val := Nat.dvd_add ha_dvd hb_dvd
      have h_p_dvd_one : p ∣ 1 := by
        have h_mod_eq : (a.val + b.val) % (p ^ n) = 1 := by omega
        -- Key: p | (a.val + b.val) % (p^n)
        -- Proof: write s = a.val + b.val. Then s % p^n = s - p^n * (s / p^n).
        -- p | s (= h_p_dvd_sum) and p | p^n * (s / p^n) (since p | p^n).
        -- So p | s - p^n * (s / p^n) = s % p^n.
        suffices p ∣ (a.val + b.val) % (p ^ n) by rwa [h_mod_eq] at this
        have h_eq : (a.val + b.val) % (p ^ n) =
            (a.val + b.val) - (p ^ n) * ((a.val + b.val) / (p ^ n)) :=
          Nat.mod_def _ _
        rw [h_eq]
        exact Nat.dvd_sub' h_p_dvd_sum
          (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : n ≠ 0)) _)
      exact Nat.Prime.not_dvd_one hp h_p_dvd_one
  }

end MathlibCandidates


/-! ## (6) The d = 1 (over GF(2)) case via maximal-ideal argument

    For F over `MvPolynomial _ (ZMod 2)` with idempotency on each
    variable, F unsat over `(ZMod 2)^n` implies `1 ∈ ⟨F⟩`.

    Proof outline (via maximal ideal):
      1. Suppose `1 ∉ ⟨F⟩`, so `⟨F⟩ ≠ ⊤`.
      2. By `Ideal.exists_le_maximal`, get `M : Ideal _` maximal
         containing `⟨F⟩`.
      3. The quotient `K := MvPolynomial _ (ZMod 2) ⧸ M` is a
         field (by `Ideal.Quotient.field`).
      4. Define `φ : Fin n → K` by `φ i := Quotient.mk M (X i)`.
      5. Idempotency on `X i` (in F ⊆ M) implies `φ i ^ 2 = φ i`
         in K. Since K is a field, this forces `φ i ∈ {0, 1}`.
      6. The map `ZMod 2 → K` is injective (ring hom from field
         to nontrivial), and {0, 1} ⊆ K is exactly the image of
         ZMod 2 (since char K = 2).
      7. So define `φ' : Fin n → ZMod 2` corresponding to φ.
      8. Then for each f ∈ F: `eval φ' f` maps to `eval φ f`
         (i.e., 0 in K) under ZMod 2 → K. Since the map is
         injective, `eval φ' f = 0` in ZMod 2.
      9. So F has a zero at φ' in `(ZMod 2)^n`. Contradicts hunsat.

    This proof would work for d = 1 but requires significant
    Lean infrastructure (ZMod 2 → K embedding, characterisation
    of {0, 1} in a char-2 field, evaluation factoring through the
    quotient). We provide the proof sketch here as a STATEMENT-ONLY.
    Mechanising it is a substantial sub-project of the full
    Song et al. theorem.
-/

/-- The d = 1 case: for `F` over `MvPolynomial _ (ZMod 2)` with
    idempotency on each variable, F unsat implies `1 ∈ ⟨F⟩`.

    Proof via maximal-ideal argument:
      1. By contradiction: assume `1 ∉ ⟨F⟩`, so `⟨F⟩ ≠ ⊤`.
      2. Get maximal `M ⊇ ⟨F⟩`.
      3. `K := MvPolynomial _ (ZMod 2) ⧸ M` is a field.
      4. Idempotency forces each `X i`'s image in K to be 0 or 1.
      5. Construct `φ' : Fin n → ZMod 2` from the images.
      6. Show `eval φ' p = 0` for each `p ∈ F` (contradicts hunsat). -/
theorem d_eq_one_completeness {n : ℕ}
    (F : Finset (MvPolynomial (Fin n) (ZMod 2)))
    (h_idemp : ∀ i : Fin n,
      (MvPolynomial.X i ^ 2 - MvPolynomial.X i :
        MvPolynomial (Fin n) (ZMod 2)) ∈ F)
    (hunsat : ∀ φ : Fin n → ZMod 2,
              ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0) :
    (1 : MvPolynomial (Fin n) (ZMod 2))
      ∈ Ideal.span (α := MvPolynomial (Fin n) (ZMod 2)) F := by
  classical
  by_contra h_not_in
  -- ⟨F⟩ ≠ ⊤
  have h_ne_top :
      Ideal.span (α := MvPolynomial (Fin n) (ZMod 2)) F ≠ ⊤ := by
    intro h_top
    apply h_not_in
    rw [h_top]; trivial
  -- Get a maximal ideal M ⊇ ⟨F⟩
  obtain ⟨M, hM_max, hM_le⟩ := Ideal.exists_le_maximal _ h_ne_top
  -- K := MvPolynomial _ (ZMod 2) ⧸ M is a field
  letI : M.IsMaximal := hM_max
  letI K_field := Ideal.Quotient.field M
  set K := MvPolynomial (Fin n) (ZMod 2) ⧸ M
  set π : MvPolynomial (Fin n) (ZMod 2) →+* K := Ideal.Quotient.mk M
  -- The image of X i in K satisfies x^2 = x (from idempotency in F ⊆ M)
  have h_idemp_K : ∀ i : Fin n, π (MvPolynomial.X i) ^ 2 = π (MvPolynomial.X i) := by
    intro i
    have h_in_M : (MvPolynomial.X i ^ 2 - MvPolynomial.X i :
        MvPolynomial (Fin n) (ZMod 2)) ∈ M := by
      exact hM_le (Ideal.subset_span (h_idemp i))
    have h_zero : π (MvPolynomial.X i ^ 2 - MvPolynomial.X i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h_in_M
    simp only [map_sub, map_pow] at h_zero
    exact sub_eq_zero.mp h_zero
  -- In a field, x^2 = x implies x = 0 or x = 1
  have h_zero_or_one : ∀ i : Fin n,
      π (MvPolynomial.X i) = 0 ∨ π (MvPolynomial.X i) = 1 := by
    intro i
    exact eq_zero_or_one_of_sq_eq_self (h_idemp_K i)
  -- Construct φ' : Fin n → ZMod 2 from the images
  -- If π(X i) = 0, set φ' i = 0; if π(X i) = 1, set φ' i = 1.
  set φ' : Fin n → ZMod 2 := fun i =>
    if h : π (MvPolynomial.X i) = 0 then 0 else 1
  -- Key: π(X i) = algebraMap (ZMod 2) K (φ' i)
  have h_phi_eq : ∀ i : Fin n,
      π (MvPolynomial.X i) = algebraMap (ZMod 2) K (φ' i) := by
    intro i
    rcases h_zero_or_one i with h | h
    · -- π(X i) = 0, φ' i = 0
      have hφ : φ' i = 0 := dif_pos h
      rw [hφ, map_zero, h]
    · -- π(X i) = 1, φ' i = 1
      have h_ne : ¬ (π (MvPolynomial.X i) = 0) := by
        rw [h]
        -- 1 ≠ 0 in K (a field). Use that M is not the whole ring.
        intro h_one_eq_zero
        have : (1 : MvPolynomial (Fin n) (ZMod 2)) ∈ M := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact h_one_eq_zero
        exact hM_max.1.1 ((Ideal.eq_top_iff_one M).mpr this)
      have hφ : φ' i = 1 := dif_neg h_ne
      rw [hφ, map_one, h]
  -- For any p ∈ F: π(p) = 0 (since p ∈ ⟨F⟩ ⊆ M)
  have h_pi_zero : ∀ p ∈ F, π p = 0 := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hM_le (Ideal.subset_span hp))
  -- Key computation: π(p) = algebraMap (ZMod 2) K (eval φ' p)
  -- This uses: π = eval₂Hom (algebraMap (ZMod 2) K) (π ∘ X)
  -- and the fact that π(X i) = algebraMap (ZMod 2) K (φ' i).
  have h_pi_eq_eval : ∀ p : MvPolynomial (Fin n) (ZMod 2),
      π p = algebraMap (ZMod 2) K (MvPolynomial.eval φ' p) := by
    intro p
    -- π is a ring hom from MvPolynomial (Fin n) (ZMod 2) to K.
    -- eval φ' is eval₂Hom (RingHom.id _) φ'.
    -- We need: π p = (algebraMap (ZMod 2) K) (eval₂Hom (RingHom.id _) φ' p)
    -- i.e., π p = eval₂Hom (algebraMap (ZMod 2) K) (algebraMap (ZMod 2) K ∘ φ') p
    -- (by comp_eval₂Hom).
    -- But also π = eval₂Hom (π.comp C) (π ∘ X) = eval₂Hom (algebraMap (ZMod 2) K) (π ∘ X)
    -- (since π.comp C = algebraMap (ZMod 2) K for the quotient).
    -- And π ∘ X = algebraMap (ZMod 2) K ∘ φ' (by h_phi_eq).
    -- So π = eval₂Hom (algebraMap (ZMod 2) K) (algebraMap (ZMod 2) K ∘ φ')
    --      = (algebraMap (ZMod 2) K).comp (eval₂Hom (RingHom.id _) φ')
    --      = (algebraMap (ZMod 2) K) ∘ (eval φ').
    have h_pi_ext : π = (algebraMap (ZMod 2) K).comp (MvPolynomial.eval φ') := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.eval_C]
        -- π (C r) = algebraMap (ZMod 2) K r
        -- π is the quotient map; C r is the image of r in MvPolynomial.
        -- algebraMap (ZMod 2) K = π.comp (MvPolynomial.C)
        -- So π (C r) = (π.comp C) r = algebraMap (ZMod 2) K r.
        show π (MvPolynomial.C r) = algebraMap (ZMod 2) K r
        rfl
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.eval_X]
        -- π (X i) = algebraMap (ZMod 2) K (φ' i)
        exact h_phi_eq i
    exact congr_fun (congr_arg DFunLike.coe h_pi_ext) p
  -- Now: for each p ∈ F, algebraMap (ZMod 2) K (eval φ' p) = 0
  -- Since algebraMap (ZMod 2) K is injective (ring hom from a field),
  -- eval φ' p = 0 for each p ∈ F.
  have h_alg_inj : Function.Injective (algebraMap (ZMod 2) K) :=
    (algebraMap (ZMod 2) K).injective
  have h_eval_zero : ∀ p ∈ F, MvPolynomial.eval φ' p = 0 := by
    intro p hp
    have := h_pi_zero p hp
    rw [h_pi_eq_eval p] at this
    exact h_alg_inj (this.trans (map_zero _).symm)
  -- This contradicts hunsat: φ' is a common zero of F.
  obtain ⟨p, hp, hp_ne⟩ := hunsat φ'
  exact hp_ne (h_eval_zero p hp)

end StrongGB
