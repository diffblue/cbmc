/-
  StrongGB.lean — Soundness of the strong Gröbner basis 2-trick
  saturation in Z_{2^d}, plus negative results showing why
  completeness is genuinely incomplete.

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/algebraic/groebner.cpp`
  (`compute`, the 2-multiple step in particular).

  ## What the C++ implementation actually does

  `groebner.cpp::compute` is a strong-GB **decision procedure
  with three possible outcomes**:

    - `UNSAT`: returned only when an **odd constant** is found
      in the saturated basis. Sound: when this happens, the
      input system genuinely has no solution.

    - `UNKNOWN`: returned when the algorithm exhausts its budget
      or saturates without producing an odd constant. The input
      may or may not have a solution; the algorithm is not making
      a claim either way.

    - (`SAT` is not currently produced by `compute` itself; it
      would come from a different code path.)

  **The implementation makes no completeness claim.** UNKNOWN is
  by design a valid result. This module formalises exactly that
  contract.

  ## Overview of formal results

  Soundness (DONE, no sorry, only standard axioms):

    1. (`two_trick_preserves_ideal`, `two_trick_preserves_ideal_mv`)
       Scalar multiplication preserves ideal membership; this
       justifies the 2-trick saturation step.

    2. (`two_trick_unsat_sound`) An odd constant in the basis
       implies the original ideal is the whole ring, i.e., UNSAT.
       Re-exported from `GroebnerSoundness.lean`.

  These two results together establish the soundness contract:
  if `compute` returns UNSAT (i.e., produces an odd constant in
  its saturated basis), then the input system is unsat.

  Negative results (DONE, no sorry, only standard axioms +
  algorithm axioms):

    3. (`naive_completeness_is_false`) The naive completeness
       statement ("F unsat ⇒ odd constant in Ideal.span F") is
       FALSE. Concrete counterexample: `d = 2, n = 0, F = {C 2}`.

    4. (`two_trick_saturation_complete_is_false`) Even adding
       the obvious well-formedness hypothesis (idempotency on
       each variable) does NOT make the natural refined
       completeness statement true. The same counterexample
       `{C 2}` defeats it (vacuously well-formed for n=0).

  These two results together show formally why UNKNOWN must be
  a valid outcome of `compute`: the algorithm cannot generally
  decide unsat, even with reasonable structural hypotheses.

  Partial completeness (DONE for the d=1 case, no sorry):

    5. (`d_eq_one_completeness`) For `d = 1` (i.e., over GF(2))
       with idempotency on each variable, F unsat over
       `(ZMod 2)^n` does imply `1 ∈ Ideal.span F`. So in this
       restricted setting completeness holds.

  ## Why we do NOT have a `two_trick_saturation_complete` theorem

  Song et al. (TACAS 2024) prove completeness for a specific
  class of polynomial systems: those arising from a faithful
  bit-vector formula encoding. Their hypothesis is much stronger
  than just "idempotency on each variable" — it ties F to the
  structure of an actual BV formula. Our `WellFormedEncoding`
  predicate (just idempotency) is genuinely too weak: see
  `two_trick_saturation_complete_is_false`.

  Mechanising the full Song et al. theorem would require:

    (a) A formal definition of bit-vector formulas and the
        encoding `BVFormula → Finset (MvPolynomial _)`.
    (b) Proof that the encoding is faithful in both directions.
    (c) The deep completeness step: under the strong hypothesis
        of (a)–(b), the strong-GB algorithm finds an odd constant.

  This is a substantial research project comparable to a
  master's thesis. It is **not** required by the implementation:
  the implementation explicitly returns UNKNOWN on inputs where
  it cannot conclude UNSAT.

  ## What this module provides

    - Soundness of the algorithm (matches the implementation's
      actual contract).
    - Negative results explaining why UNKNOWN is necessary.
    - The d=1 special case (a positive completeness result with
      a concrete restriction).
    - Several mathlib-contributable lemmas (see
      MATHLIB_CANDIDATES.md).
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

/-- **NEGATIVE RESULT**: the "obvious" refined completeness statement
    — adding only `WellFormedEncoding F` (idempotency on each
    variable) — is **also FALSE**.

    Concretely: `(d=2, n=0, F={C 2})` satisfies all hypotheses
    (`WellFormedEncoding` is vacuously true for `n = 0`) but
    has no odd constant in `Ideal.span F`, hence none in
    `strongGB F` (since `strongGB_ideal_preserved` says
    `Ideal.span (strongGB F) = Ideal.span F`).

    This shows that the `WellFormedEncoding` predicate as
    currently defined is too weak to capture the structural
    requirements of an actual BV encoding. The Song et al.
    completeness theorem requires a much stronger hypothesis:
    `F` must arise from a genuine bit-vector formula encoding,
    not just be a collection of polynomials with idempotency.

    To turn this into a true theorem, `WellFormedEncoding` must
    be strengthened to include enough of the BV-encoding
    structure that it rules out trivial counterexamples like
    `F = {C 2}`. A minimal example of a strengthening that
    works: require that for every constant `C r ∈ F`, `r` is
    a multiple of `2^d` (so adding constants forces ⟨F⟩ = ⟨0⟩
    or contains `C 1`). But the actual Song et al. hypothesis
    is more subtle and tied to the BV-formula structure. -/
theorem two_trick_saturation_complete_is_false :
    ¬ (∀ {n d : ℕ} (_hd : 0 < d)
         (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d))))
         (_hwf : WellFormedEncoding F)
         (_hunsat : ∀ φ : Fin n → ZMod (2 ^ d),
                    ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0),
         ∃ c : ℕ, ¬ 2 ∣ c ∧
           (MvPolynomial.C (c : ZMod (2 ^ d))
             : MvPolynomial (Fin n) (ZMod (2 ^ d))) ∈ strongGB F) := by
  intro h_universal
  -- Apply to F = {C 2} ⊆ MvPoly (Fin 0) (ZMod (2^2)).
  set F : Finset (MvPolynomial (Fin 0) (ZMod (2 ^ 2))) :=
    {MvPolynomial.C 2} with hF_def
  have h_unsat : ∀ φ : Fin 0 → ZMod (2 ^ 2),
      ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0 := by
    intro φ
    refine ⟨MvPolynomial.C 2, Finset.mem_singleton.mpr rfl, ?_⟩
    show (MvPolynomial.eval φ) (MvPolynomial.C (2 : ZMod (2 ^ 2))) ≠ 0
    rw [MvPolynomial.eval_C]
    show (2 : ZMod (2 ^ 2)) ≠ 0
    decide
  have h_wf : WellFormedEncoding (n := 0) (d := 2) F := fun i => i.elim0
  obtain ⟨c, hc_odd, hc_mem⟩ := h_universal (n := 0) (d := 2) (by norm_num) F h_wf h_unsat
  -- C c ∈ strongGB F ⊆ Ideal.span (strongGB F) = Ideal.span F.
  have hc_in_span : (MvPolynomial.C (c : ZMod (2 ^ 2))
        : MvPolynomial (Fin 0) (ZMod (2 ^ 2)))
        ∈ Ideal.span ((F : Set (MvPolynomial (Fin 0) (ZMod (2 ^ 2))))) := by
    rw [← strongGB_ideal_preserved (n := 0) (d := 2) F]
    exact Ideal.subset_span hc_mem
  -- Apply the ring iso to reduce to ZMod 4.
  let φ := MvPolynomial.isEmptyRingEquiv (ZMod (2 ^ 2)) (Fin 0)
  have h_phi_C : ∀ r : ZMod (2 ^ 2), φ (MvPolynomial.C r) = r := by
    intro r
    show (MvPolynomial.isEmptyAlgEquiv (ZMod (2 ^ 2)) (Fin 0))
            (MvPolynomial.C r) = r
    simp [MvPolynomial.isEmptyAlgEquiv]
  have h_F_set : (F : Set (MvPolynomial (Fin 0) (ZMod (2 ^ 2))))
              = ({MvPolynomial.C 2}
                : Set (MvPolynomial (Fin 0) (ZMod (2 ^ 2)))) := by
    rw [hF_def]; simp
  rw [h_F_set] at hc_in_span
  have h_image : (c : ZMod (2 ^ 2))
        ∈ Ideal.span ({(2 : ZMod (2 ^ 2))} : Set (ZMod (2 ^ 2))) := by
    rw [show ((c : ZMod (2 ^ 2)) : ZMod (2 ^ 2))
            = φ (MvPolynomial.C (c : ZMod (2 ^ 2))) from (h_phi_C _).symm,
        show (2 : ZMod (2 ^ 2)) = φ (MvPolynomial.C 2) from (h_phi_C _).symm]
    have h_iso : Ideal.map φ.toRingHom
            (Ideal.span
              ({MvPolynomial.C 2} : Set (MvPolynomial (Fin 0) (ZMod (2 ^ 2)))))
          = Ideal.span ({φ (MvPolynomial.C 2)} : Set (ZMod (2 ^ 2))) := by
      rw [Ideal.map_span]; simp
    rw [← h_iso]
    exact Ideal.mem_map_of_mem φ.toRingHom hc_in_span
  -- Convert ZMod (2^2) to ZMod 4 numerically.
  have h_image' : (c : ZMod 4) ∈ Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)) := by
    convert h_image using 2
  exact odd_not_in_two_ideal_zmod_four hc_odd h_image'





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


/-! ## (7) Mod-2 reduction: connecting d > 1 to d = 1

    Key insight: with `WellFormedEncoding` (idempotency on each
    variable), the only valid assignments in `(ZMod (2^d))^n` are
    in `{0, 1}^n`. This is because `x^2 = x` in `ZMod (2^d)` for
    `d ≥ 1` forces `x ∈ {0, 1}` (proven below).

    Consequence: "F unsat over `(ZMod (2^d))^n`" with idempotency
    is equivalent to "F unsat over `{0, 1}^n`", which (via the
    embedding `{0, 1} ↪ ZMod 2`) is equivalent to "F mod 2 unsat
    over `(ZMod 2)^n`".
-/

/-- In `ZMod (2^d)` for `d ≥ 1`, `x^2 = x` implies `x = 0 ∨ x = 1`.

    MATHLIB CANDIDATE. This generalises `eq_zero_or_one_of_sq_eq_self`
    (which requires `CancelMonoidWithZero`, i.e., no zero divisors)
    to the non-domain `ZMod (2^d)` for `d ≥ 2`.

    Proof: `x(x-1) = 0` in `ZMod (2^d)` means `2^d | x.val*(x.val-1)`.
    Since consecutive integers are coprime, `2^d` divides one factor.
    Both factors are < 2^d, so the divisible one must be 0. -/
theorem sq_eq_self_of_zmod_two_pow {d : ℕ} (hd : 0 < d) (x : ZMod (2 ^ d))
    (hx : x ^ 2 = x) : x = 0 ∨ x = 1 := by
  haveI : NeZero (2 ^ d) := ⟨by have := Nat.one_lt_pow (by omega : d ≠ 0)
                                          (by norm_num : 1 < 2); omega⟩
  haveI : Fact (1 < 2 ^ d) := ⟨Nat.one_lt_pow (by omega) (by norm_num)⟩
  -- x^2 = x means x * (x - 1) = 0 in ZMod (2^d)
  have h_prod : x * (x - 1) = 0 := by
    have h2 : x * (x - 1) = x ^ 2 - x := by ring
    rw [h2, sub_eq_zero.mpr hx]
  by_cases hx_zero : x.val = 0
  · left
    rw [← ZMod.natCast_zmod_val x, hx_zero, Nat.cast_zero]
  · right
    have hx_pos : 0 < x.val := Nat.pos_of_ne_zero hx_zero
    have hx_lt : x.val < 2 ^ d := ZMod.val_lt x
    -- (x - 1).val = x.val - 1 (since 1 ≤ x.val < 2^d)
    have h_sub_val : (x - 1).val = x.val - 1 := by
      have h1_val : (1 : ZMod (2 ^ d)).val = 1 := ZMod.val_one _
      have h1_le : (1 : ZMod (2 ^ d)).val ≤ x.val := by omega
      have := ZMod.val_sub h1_le
      rw [h1_val] at this
      exact this
    -- x * (x-1) = 0 means 2^d | x.val * (x.val - 1)
    have h_prod_zero : (x.val * (x.val - 1)) % (2 ^ d) = 0 := by
      have h_prod_val : (x * (x - 1)).val = (x.val * (x - 1).val) % (2 ^ d) :=
        ZMod.val_mul x (x - 1)
      rw [h_sub_val] at h_prod_val
      have := congrArg ZMod.val h_prod
      rw [h_prod_val, ZMod.val_zero] at this
      exact this
    have h_dvd_prod : 2 ^ d ∣ x.val * (x.val - 1) :=
      Nat.dvd_of_mod_eq_zero h_prod_zero
    -- Case split: 2 | x.val or not
    by_cases h2x : 2 ∣ x.val
    · -- 2 | x.val, so 2 ∤ (x.val - 1), so Coprime (2^d) (x.val - 1)
      have h2_not_xm1 : ¬ 2 ∣ (x.val - 1) := by omega
      have h_cop : Nat.Coprime (2 ^ d) (x.val - 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra h_ne
        have h_exists := Nat.exists_prime_and_dvd h_ne
        obtain ⟨q, hq_prime, hq_dvd⟩ := h_exists
        have hq_dvd_2d : q ∣ 2 ^ d := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
        have hq_dvd_xm1 : q ∣ x.val - 1 := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
        have hq_eq_2 : q = 2 :=
          (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 2) q
            (hq_prime.dvd_of_dvd_pow hq_dvd_2d)).resolve_left hq_prime.one_lt.ne'
        exact h2_not_xm1 (hq_eq_2 ▸ hq_dvd_xm1)
      -- Coprime (2^d) (x.val-1) and 2^d | x.val * (x.val-1) → 2^d | x.val
      have h_dvd_x : 2 ^ d ∣ x.val := h_cop.dvd_of_dvd_mul_right h_dvd_prod
      -- But x.val < 2^d and x.val > 0, contradiction.
      exact absurd (Nat.eq_zero_of_dvd_of_lt h_dvd_x hx_lt) hx_zero
    · -- 2 ∤ x.val, so Coprime (2^d) x.val
      have h_cop : Nat.Coprime (2 ^ d) x.val := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra h_ne
        have h_exists := Nat.exists_prime_and_dvd h_ne
        obtain ⟨q, hq_prime, hq_dvd⟩ := h_exists
        have hq_dvd_2d : q ∣ 2 ^ d := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
        have hq_dvd_x : q ∣ x.val := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
        have hq_eq_2 : q = 2 :=
          (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 2) q
            (hq_prime.dvd_of_dvd_pow hq_dvd_2d)).resolve_left hq_prime.one_lt.ne'
        exact h2x (hq_eq_2 ▸ hq_dvd_x)
      -- Coprime (2^d) x.val and 2^d | x.val * (x.val-1) → 2^d | (x.val-1)
      have h_dvd_xm1 : 2 ^ d ∣ (x.val - 1) := h_cop.dvd_of_dvd_mul_left h_dvd_prod
      have : x.val - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h_dvd_xm1 (by omega)
      rw [← ZMod.natCast_zmod_val x, show x.val = 1 from by omega]; simp


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
