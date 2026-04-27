/-
  Mechanized soundness proofs for the algebraic solver's UNSAT
  reporting in the strong Gröbner basis computation over Z_{2^d}.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

/-! ## Lemma 2: Unit in ideal implies 1 in ideal -/

theorem unit_mem_ideal_implies_one_mem {R : Type*} [CommRing R]
    (I : Ideal R) {u : R} (hu : IsUnit u) (hm : u ∈ I) :
    (1 : R) ∈ I := by
  obtain ⟨u', rfl⟩ := hu
  have : (↑u'⁻¹ : R) * ↑u' = 1 := by simp [Units.inv_mul]
  rw [← this]
  exact I.mul_mem_left ↑u'⁻¹ hm

theorem ideal_eq_top_of_unit_mem {R : Type*} [CommRing R]
    (I : Ideal R) {u : R} (hu : IsUnit u) (hm : u ∈ I) :
    I = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact unit_mem_ideal_implies_one_mem I hu hm

/-! ## Lemma 3a: Rabinowitsch satisfiable when difference is a unit -/

theorem exists_mul_eq_one_of_isUnit' {R : Type*} [CommRing R]
    {d : R} (h : IsUnit d) :
    ∃ e : R, d * e = 1 := by
  obtain ⟨u, hu⟩ := h
  exact ⟨↑u⁻¹, by rw [← hu]; simp [Units.mul_inv]⟩

/-! ## Lemma 3b: Odd naturals are units in Z_{2^d} -/

theorem Nat.coprime_pow_two_of_odd {a d : ℕ} (ha : ¬ 2 ∣ a) :
    Nat.Coprime a (2 ^ d) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr ha).symm.pow_right d

theorem ZMod.isUnit_of_odd_nat {d a : ℕ} (ha : ¬ 2 ∣ a) :
    IsUnit (a : ZMod (2 ^ d)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.coprime_pow_two_of_odd ha

/-! ## Main soundness theorems -/

theorem no_solution_if_ideal_is_top {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) (htop : I = ⊤) :
    (1 : R) ∈ I ∧ (1 : R) ≠ (0 : R) :=
  ⟨htop ▸ Submodule.mem_top, one_ne_zero⟩

theorem ideal_ne_top_of_has_solution {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial S]
    (I : Ideal R) (φ : R →+* S) (hφ : ∀ f ∈ I, φ f = 0) :
    I ≠ ⊤ := by
  intro htop
  have h1 : (1 : R) ∈ I := htop ▸ Submodule.mem_top
  have := hφ 1 h1
  simp at this

/-- The complete soundness chain for Z_{2^d}: odd constant in basis
    → unit in ideal → I = ⊤ → no solution exists. -/
theorem soundness_of_odd_constant_check {d : ℕ}
    (I : Ideal (ZMod (2 ^ d))) {c : ℕ} (hc_odd : ¬ 2 ∣ c)
    (hc_mem : (c : ZMod (2 ^ d)) ∈ I) :
    I = ⊤ :=
  ideal_eq_top_of_unit_mem I (ZMod.isUnit_of_odd_nat hc_odd) hc_mem
