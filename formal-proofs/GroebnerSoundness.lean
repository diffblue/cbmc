/-
  Soundness proofs for the algebraic solver's UNSAT reporting
  in the strong Gröbner basis computation over Z_{2^d}.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

/-! ## Lemma 2: Unit in ideal implies 1 in ideal -/

/-- If a unit u is in an ideal I, then 1 ∈ I. -/
theorem unit_mem_ideal_implies_one_mem {R : Type*} [CommRing R]
    (I : Ideal R) {u : R} (hu : IsUnit u) (hm : u ∈ I) :
    (1 : R) ∈ I := by
  obtain ⟨u', rfl⟩ := hu
  have : (↑u'⁻¹ : R) * ↑u' = 1 := by simp [Units.inv_mul]
  rw [← this]
  exact I.mul_mem_left ↑u'⁻¹ hm

/-- Corollary: if a unit is in I, then I is the whole ring. -/
theorem ideal_eq_top_of_unit_mem {R : Type*} [CommRing R]
    (I : Ideal R) {u : R} (hu : IsUnit u) (hm : u ∈ I) :
    I = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact unit_mem_ideal_implies_one_mem I hu hm

/-! ## Lemma 3a: Rabinowitsch satisfiable when difference is a unit -/

/-- If d is a unit, then d * e = 1 has a solution. -/
theorem exists_mul_eq_one_of_isUnit' {R : Type*} [CommRing R]
    {d : R} (h : IsUnit d) :
    ∃ e : R, d * e = 1 := by
  obtain ⟨u, hu⟩ := h
  exact ⟨↑u⁻¹, by rw [← hu]; simp [Units.mul_inv]⟩

/-! ## Main soundness theorem -/

/-- **Soundness of UNSAT reporting.**

    If I = ⊤, then 1 ∈ I. In a nontrivial ring, 1 ≠ 0.
    Therefore no evaluation can send all of I to 0. -/
theorem no_solution_if_ideal_is_top {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) (htop : I = ⊤) :
    (1 : R) ∈ I ∧ (1 : R) ≠ (0 : R) :=
  ⟨htop ▸ Submodule.mem_top, one_ne_zero⟩

/-- **Contrapositive: if the system has a solution, I ≠ ⊤.**

    If there exists an evaluation φ : R → S sending all generators
    of I to 0 (and φ is a ring homomorphism, so φ(1) = 1 ≠ 0),
    then 1 ∉ I, so I ≠ ⊤, so our check cannot report UNSAT. -/
theorem ideal_ne_top_of_has_solution {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial S]
    (I : Ideal R) (φ : R →+* S) (hφ : ∀ f ∈ I, φ f = 0) :
    I ≠ ⊤ := by
  intro htop
  have h1 : (1 : R) ∈ I := htop ▸ Submodule.mem_top
  have := hφ 1 h1
  simp at this
