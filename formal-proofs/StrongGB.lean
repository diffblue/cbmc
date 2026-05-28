/-
  StrongGB.lean — Soundness of the strong Gröbner basis 2-trick
  saturation in Z_{2^d}.

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/algebraic/groebner.cpp`
  (`compute`, the 2-multiple step in particular).

  ## What this module covers

  Single-variable / scalar facts (DONE, no sorry):

    1. (`two_trick_preserves_ideal`) Scalar multiplication
       preserves ideal membership. Trivial, follows from
       Mathlib's `Ideal.mul_mem_right`. Justifies the
       implementation's 2-trick step at the basis level: doubling
       (or 2^k-multiplying) any polynomial in the basis yields
       another polynomial in the same ideal.

    2. (`two_trick_unsat_sound`) The existing soundness chain
       (odd constant in basis ⇒ unit ⇒ ideal = ⊤ ⇒ original
       system UNSAT) re-exported from `GroebnerSoundness.lean`.

  Multivariate completeness statement (STATEMENT-ONLY):

    3. (`two_trick_saturation_complete`) For any unsatisfiable
       polynomial system `F ⊆ MvPolynomial (Fin n) (ZMod (2^d))`,
       the strong Gröbner basis algorithm with 2-trick saturation
       produces a basis containing an odd constant. **This is the
       deep theorem.** Statement provided; proof admitted.

  ## Why the multivariate completeness is hard

  Mathlib's `Mathlib.RingTheory.MvPolynomial.Groebner` provides the
  classical division algorithm assuming all leading coefficients
  are units (`hb : ∀ i, IsUnit (m.leadingCoeff (b i))`). This works
  for fields and for the strong-saturation-free case but **fails
  for `ZMod (2^d)`**, whose leading coefficient might be `2`, `4`,
  ..., none of which is a unit.

  Song et al. (TACAS 2024) extend the classical theory by adding
  the **2-trick saturation rule**: when reducing a polynomial `f`
  by a polynomial `b` whose leading coefficient is `2^k * u`
  (with `u` a unit and `k > 0`), instead of giving up, also
  include `(2^(d-k)) * b` in the basis. This `2^(d-k) * b` has
  zero in position `k`...`d-1` of its coefficient (mod `2^d`),
  effectively saturating the ideal along the powers-of-2 axis.

  Their completeness theorem says: with this saturation, the
  algorithm catches every UNSAT certificate over `ZMod (2^d)`.

  ## What infrastructure is needed to fully mechanise

  To prove `two_trick_saturation_complete` from scratch in Lean
  one would need:

    (a) **Strong leading-coefficient handling**. Generalise
        Mathlib's division algorithm to allow leading coefficients
        in `ZMod (2^d)`. Specifically, replace the
        `IsUnit (m.leadingCoeff b)` hypothesis with a 2-adic-
        valuation-aware reduction step.

    (b) **The 2-trick saturation step** as a Lean function. Given
        a polynomial `b` with `m.leadingCoeff b = 2^k * u` (`u` a
        unit), produce `2^(d-k) * b` and add it to the basis.

    (c) **Termination** of the strong-GB algorithm over
        `ZMod (2^d)`. The classical Buchberger termination uses
        ascending chain on monomial ideals. The strong version
        needs ascending chain on a refined ordering that tracks
        the 2-adic valuation of leading coefficients. Mathlib's
        Noetherian-ring infrastructure (`Mathlib.RingTheory.Noetherian`)
        plus 2-adic-valuation lemmas should suffice.

    (d) **Soundness** of strong-GB: ⟨G⟩ = ⟨F⟩ at termination.
        Direct from termination + ideal-preserving steps; this is
        already the bulk of `BuchbergerCorrectness.lean`, just
        extended to the saturation step (which is also
        ideal-preserving by `two_trick_preserves_ideal` below).

    (e) **Completeness**: for `F` unsatisfiable on
        `(ZMod (2^d))^n`, strong-GB(F) contains an odd constant.
        This is the **deep step** — the Song et al. theorem.
        It does NOT follow from Hilbert's Nullstellensatz
        (which is for fields), nor from a reduction to `ZMod 2`
        (which loses information for `d > 1`). The proof
        requires an explicit construction of the odd constant
        from a satisfiability certificate.

  Estimated work to mechanise: parts (a)–(d) are perhaps 1–2
  months of focused Lean work. Part (e) is the genuine research
  contribution and likely 3–6 months on top, comparable to a
  master's thesis. We provide the precise statement here as a
  scaffold.
-/

import GroebnerSoundness
import BuchbergerCorrectness
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
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

/-- The same fact lifted to `MvPolynomial (Fin n) (ZMod (2^d))`,
    which is the setting of the implementation's polynomials. -/
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

/-! ## (3) The deep claim: strong-GB completeness over ZMod (2^d)

    To state the completeness theorem precisely we need to define
    what the strong-GB algorithm produces. Below we declare
    `strongGB` axiomatically (matching the implementation), then
    state what its output should satisfy.
-/

/-- The strong-GB algorithm: given a finite polynomial set `F`
    over `MvPolynomial (Fin n) (ZMod (2^d))`, returns the strong
    Gröbner basis. Declared axiomatically here to match the
    implementation in `groebner.cpp::compute`. -/
axiom strongGB {n d : ℕ} :
    Finset (MvPolynomial (Fin n) (ZMod (2 ^ d))) →
    Finset (MvPolynomial (Fin n) (ZMod (2 ^ d)))

/-- Soundness axiom: strongGB preserves the ideal generated. This
    is the part that follows from existing proofs (the
    BuchbergerCorrectness chain extended to the 2-trick step,
    which preserves ideal membership by
    `two_trick_preserves_ideal_mv` above). Stated axiomatically
    here pending mechanisation of items (c)+(d) above. -/
axiom strongGB_ideal_preserved {n d : ℕ}
    (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d)))) :
    Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) (strongGB F)
    = Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) F

/-- The deep claim: COMPLETENESS of strong-GB over `ZMod (2^d)`.

    IMPL: src/solvers/algebraic/groebner.cpp::compute
    (the strong-GB algorithm with 2-trick saturation).

    For any polynomial system `F` over
    `MvPolynomial (Fin n) (ZMod (2^d))` that has no zero in
    `(ZMod (2^d))^n`, the strong-GB algorithm produces a basis
    containing an odd constant.

    This is the precise version of the Song et al. (TACAS 2024)
    completeness theorem. The proof requires items (a)–(e) from
    the module docstring; we state it here as STATEMENT-ONLY
    and admit the proof. -/
theorem two_trick_saturation_complete {n d : ℕ} (hd : 0 < d)
    (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d))))
    (hunsat : ∀ φ : Fin n → ZMod (2 ^ d),
              ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0) :
    ∃ c : ℕ, ¬ 2 ∣ c ∧
      (MvPolynomial.C (c : ZMod (2 ^ d))
        : MvPolynomial (Fin n) (ZMod (2 ^ d))) ∈ strongGB F := by
  sorry

/-- Corollary at the ideal level: combining completeness +
    soundness gives `Ideal.span F = ⊤` for unsat systems. This
    matches the existing soundness chain via the odd-constant
    witness. -/
theorem unsat_implies_ideal_top {n d : ℕ} (hd : 0 < d)
    (F : Finset (MvPolynomial (Fin n) (ZMod (2 ^ d))))
    (hunsat : ∀ φ : Fin n → ZMod (2 ^ d),
              ∃ p ∈ F, MvPolynomial.eval φ p ≠ 0) :
    Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) F = ⊤ := by
  -- From completeness, strongGB F contains some odd constant c.
  obtain ⟨c, hc_odd, hc_mem⟩ := two_trick_saturation_complete hd F hunsat
  -- From soundness, that constant is in the ideal generated by F.
  have h_in_F :
      (MvPolynomial.C (c : ZMod (2 ^ d))
        : MvPolynomial (Fin n) (ZMod (2 ^ d)))
        ∈ Ideal.span (α := MvPolynomial (Fin n) (ZMod (2 ^ d))) F := by
    rw [← strongGB_ideal_preserved F]
    exact Ideal.subset_span hc_mem
  -- The constant `(c : ZMod (2^d))` is a unit (odd ⇒ unit), so its
  -- image under MvPolynomial.C is a unit in MvPolynomial. The ideal
  -- containing a unit is ⊤.
  have h_unit_zmod : IsUnit (c : ZMod (2 ^ d)) :=
    ZMod.isUnit_of_odd_nat hc_odd
  have h_unit :
      IsUnit (MvPolynomial.C (c : ZMod (2 ^ d))
              : MvPolynomial (Fin n) (ZMod (2 ^ d))) :=
    h_unit_zmod.map MvPolynomial.C
  exact Ideal.eq_top_of_isUnit_mem _ h_in_F h_unit

end StrongGB
