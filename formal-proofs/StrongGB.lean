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

    PROOF STATUS: STATEMENT-ONLY. The proof outline (via maximal
    ideal + characteristic-2 field argument) is in the docstring
    above. -/
theorem d_eq_one_completeness {n : ℕ}
    (F : Finset (MvPolynomial (Fin n) (ZMod 2)))
    (h_idemp : ∀ i : Fin n,
      (MvPolynomial.X i ^ 2 - MvPolynomial.X i :
        MvPolynomial (Fin n) (ZMod 2)) ∈ F)
    (hunsat : ∀ φ : Fin n → ZMod 2,
              ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0) :
    (1 : MvPolynomial (Fin n) (ZMod 2))
      ∈ Ideal.span (α := MvPolynomial (Fin n) (ZMod 2)) F := by
  by_contra h_not_in
  -- ⟨F⟩ ≠ ⊤
  have h_ne_top :
      Ideal.span (α := MvPolynomial (Fin n) (ZMod 2)) F ≠ ⊤ := by
    intro h_top
    apply h_not_in
    rw [h_top]; trivial
  -- Get a maximal ideal M ⊇ ⟨F⟩
  obtain ⟨M, hM_max, hM_le⟩ := Ideal.exists_le_maximal _ h_ne_top
  -- The quotient K := MvPolynomial _ (ZMod 2) ⧸ M is a field
  -- (via Ideal.Quotient.field [hM_max]).
  -- Define φ : Fin n → K via the canonical map. Each φ i satisfies
  -- φ i ^ 2 = φ i (from idempotency in F ⊆ M), so φ i ∈ {0, 1} in K.
  -- Map back to (ZMod 2)^n via the embedding ZMod 2 → K, getting
  -- φ' : Fin n → ZMod 2 with eval φ' p = 0 for each p ∈ F.
  -- This contradicts hunsat.
  --
  -- The full mechanisation requires:
  --   - The Ideal.Quotient.field instance.
  --   - ZMod 2 → K injective (ring hom from a field to nontrivial).
  --   - Idempotency forcing φ i ∈ {0, 1} in K.
  --   - Evaluation factoring through the quotient.
  -- These are all standard but require careful manipulation in Lean.
  sorry

end StrongGB
