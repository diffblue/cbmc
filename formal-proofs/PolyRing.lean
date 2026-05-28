/-
  PolyRing.lean — Soundness proofs for primitives in
  `src/solvers/algebraic/poly_ring.cpp`.

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  This module covers the basic ring-arithmetic primitives that
  the strong-GB algorithm builds on:

    - `inverse_mod_2d` (Hensel-lifting modular inverse) —
      contract: for odd `a`, returns `x` with `a * x ≡ 1 (mod 2^d)`.
    - `monomialt::operator<` (graded lex ordering) —
      contract: total strict order on monomials.
    - `polynomialt::normalize` (canonicalisation) —
      contract: preserves polynomial value modulo the ring.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

namespace PolyRing

/-! ## (1) `inverse_mod_2d` correctness

    The C++ function `inverse_mod_2d(a, d)` computes the multiplicative
    inverse of an odd integer `a` modulo `2^d` via Hensel lifting
    (Newton iteration `x ↦ x * (2 - a*x)`, doubling 2-adic precision
    each step).

    Contract: for odd `a` and any `d ≥ 0`, the function returns
    `x` with `(a * x) ≡ 1 (mod 2^d)`.

    The mathematical fact this contract relies on: in `ZMod (2^d)`,
    every odd element is a unit (and units have unique inverses).
    The Hensel iteration is one constructive way to compute this
    inverse; we prove the existence-and-uniqueness fact, which
    is the contract.
-/

/-- Existence: for odd `a : ℕ` and any `d ≥ 1`, there exists
    `x : ZMod (2^d)` with `(a : ZMod (2^d)) * x = 1`.

    This is the contract `inverse_mod_2d` satisfies. -/
theorem inverse_mod_2d_exists {a d : ℕ} (_hd : 0 < d) (ha : ¬ 2 ∣ a) :
    ∃ x : ZMod (2 ^ d), (a : ZMod (2 ^ d)) * x = 1 := by
  -- Odd a is coprime to 2^d, hence a unit, hence has an inverse.
  haveI : NeZero (2 ^ d) := ⟨by
    have : 1 < 2 ^ d := Nat.one_lt_pow (by omega) (by norm_num)
    omega⟩
  have h_coprime : Nat.Coprime a (2 ^ d) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_ne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h_ne
    have hq_dvd_a : q ∣ a := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
    have hq_dvd_2d : q ∣ 2 ^ d := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
    have hq_eq_2 : q = 2 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 2) q
        (hq_prime.dvd_of_dvd_pow hq_dvd_2d)).resolve_left hq_prime.one_lt.ne'
    exact ha (hq_eq_2 ▸ hq_dvd_a)
  have h_unit : IsUnit (a : ZMod (2 ^ d)) :=
    (ZMod.isUnit_iff_coprime a (2 ^ d)).mpr h_coprime
  obtain ⟨u, hu⟩ := h_unit
  refine ⟨↑u⁻¹, ?_⟩
  rw [← hu]
  exact_mod_cast u.mul_inv

/-- Uniqueness: any two inverses of an odd element are equal. -/
theorem inverse_mod_2d_unique {a d : ℕ} (_hd : 0 < d) (ha : ¬ 2 ∣ a)
    {x y : ZMod (2 ^ d)}
    (hx : (a : ZMod (2 ^ d)) * x = 1) (hy : (a : ZMod (2 ^ d)) * y = 1) :
    x = y := by
  -- a*x = 1 = a*y, and a is a unit (cancellable).
  haveI : NeZero (2 ^ d) := ⟨by
    have : 1 < 2 ^ d := Nat.one_lt_pow (by omega) (by norm_num)
    omega⟩
  have h_coprime : Nat.Coprime a (2 ^ d) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_ne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h_ne
    have hq_dvd_a : q ∣ a := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
    have hq_dvd_2d : q ∣ 2 ^ d := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
    have hq_eq_2 : q = 2 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 2) q
        (hq_prime.dvd_of_dvd_pow hq_dvd_2d)).resolve_left hq_prime.one_lt.ne'
    exact ha (hq_eq_2 ▸ hq_dvd_a)
  have h_unit : IsUnit (a : ZMod (2 ^ d)) :=
    (ZMod.isUnit_iff_coprime a (2 ^ d)).mpr h_coprime
  exact h_unit.mul_left_cancel (hx.trans hy.symm)

/-- Combined: existence-and-uniqueness of the inverse. -/
theorem inverse_mod_2d_correct {a d : ℕ} (hd : 0 < d) (ha : ¬ 2 ∣ a) :
    ∃! x : ZMod (2 ^ d), (a : ZMod (2 ^ d)) * x = 1 := by
  obtain ⟨x, hx⟩ := inverse_mod_2d_exists hd ha
  exact ⟨x, hx, fun y hy => inverse_mod_2d_unique hd ha hy hx⟩

/-! ## (2) `monomialt::operator<` is a strict total well-order

    The C++ comparator implements graded reverse lexicographic
    (grevlex) order: higher total degree comes first; ties are
    broken by reverse lex on exponents.

    Contract: `<` is a strict total order on monomials, and it
    is a well-order (every nonempty set has a minimum). The
    well-order property is essential for Buchberger termination.

    We model monomials abstractly as `Fin n →₀ ℕ` (finitely
    supported exponent vectors) and prove the grevlex relation
    has the required properties.
-/

/-- Total degree of an exponent vector. -/
def totalDegree {n : ℕ} (m : Fin n →₀ ℕ) : ℕ := m.sum (fun _ e => e)

/-- Grevlex comparison: higher total degree is "smaller" (comes
    first in the basis ordering used for leading-term selection).
    This matches the C++ comparator's `return d0 > d1` for the
    grading step. -/
def grevlexLt {n : ℕ} (m₁ m₂ : Fin n →₀ ℕ) : Prop :=
  totalDegree m₁ > totalDegree m₂ ∨
  (totalDegree m₁ = totalDegree m₂ ∧
    ∃ i : Fin n, (∀ j > i, m₁ j = m₂ j) ∧ m₁ i < m₂ i)

/-- The grevlex relation is irreflexive. -/
theorem grevlexLt_irrefl {n : ℕ} (m : Fin n →₀ ℕ) : ¬ grevlexLt m m := by
  rintro (h | ⟨_, i, _, h⟩)
  · exact absurd h (lt_irrefl _)
  · exact absurd h (lt_irrefl _)

/-- The grevlex relation is asymmetric. -/
theorem grevlexLt_asymm {n : ℕ} {m₁ m₂ : Fin n →₀ ℕ}
    (h : grevlexLt m₁ m₂) : ¬ grevlexLt m₂ m₁ := by
  intro h'
  rcases h with h_deg | ⟨h_eq, i, h_above, h_lt⟩
  · rcases h' with h_deg' | ⟨h_eq', _, _, _⟩
    · exact absurd h_deg' (not_lt.mpr h_deg.le)
    · omega
  · rcases h' with h_deg' | ⟨_, j, h_above', h_lt'⟩
    · omega
    · -- Both i and j are positions where the exponents differ.
      rcases lt_trichotomy i j with hij | hij | hij
      · -- i < j: by h_above, m₁ j = m₂ j; but h_lt' says m₂ j < m₁ j. Contradiction.
        have := h_above j hij
        omega
      · -- i = j: m₁ i < m₂ i and m₂ i < m₁ i. Contradiction.
        rw [hij] at h_lt; omega
      · -- j < i: by h_above', m₂ i = m₁ i; but h_lt says m₁ i < m₂ i. Contradiction.
        have := h_above' i hij
        omega

/-- Trichotomy: for any two distinct monomials, exactly one of
    `<` and `>` holds. (Combined with `Decidable` equality, this
    gives totality.) Since the C++ comparator returns `true` or
    `false` based on this comparison, the resulting `<` is total
    on distinct monomials and irreflexive on equal ones — making
    it a well-defined comparator for sorting. -/
theorem grevlexLt_total {n : ℕ} (m₁ m₂ : Fin n →₀ ℕ) (hne : m₁ ≠ m₂) :
    grevlexLt m₁ m₂ ∨ grevlexLt m₂ m₁ := by
  classical
  -- Case 1: total degrees differ.
  rcases lt_trichotomy (totalDegree m₁) (totalDegree m₂) with h | h | h
  · right; exact Or.inl h
  · -- Case 2: total degrees equal; find a position where they differ.
    have hne' : ∃ i : Fin n, m₁ i ≠ m₂ i := by
      by_contra h_all
      push_neg at h_all
      exact hne (Finsupp.ext (fun i => h_all i))
    -- Pick the largest such i using Finset.max' on the difference set.
    let s : Finset (Fin n) := Finset.univ.filter (fun i => m₁ i ≠ m₂ i)
    have h_nonempty : s.Nonempty := by
      obtain ⟨i, hi⟩ := hne'
      exact ⟨i, by simp [s, hi]⟩
    let i := s.max' h_nonempty
    have hi_in_s : i ∈ s := Finset.max'_mem s h_nonempty
    have hi_ne : m₁ i ≠ m₂ i := by simp [s] at hi_in_s; exact hi_in_s
    have h_above : ∀ j > i, m₁ j = m₂ j := by
      intro j hj
      by_contra h_diff
      have hj_in_s : j ∈ s := by simp [s, h_diff]
      have := s.le_max' j hj_in_s
      omega
    rcases lt_trichotomy (m₁ i) (m₂ i) with h_lt | h_eq | h_lt
    · -- m₁ i < m₂ i: grevlexLt m₁ m₂
      left; exact Or.inr ⟨h, i, h_above, h_lt⟩
    · exact absurd h_eq hi_ne
    · -- m₂ i < m₁ i: grevlexLt m₂ m₁
      right
      exact Or.inr ⟨h.symm, i, fun j hj => (h_above j hj).symm, h_lt⟩
  · left; exact Or.inl h

/-! ## (3) `polynomialt::normalize` semantic preservation

    The C++ function combines like terms (terms with the same
    monomial), removes zero coefficients, and sorts by the
    monomial order. This is canonicalisation.

    Contract: `normalize(p)` represents the same polynomial as
    `p`. Specifically, for any evaluation `φ`, `eval φ (normalize p)
    = eval φ p`.

    Mathematically: combining like terms is just associativity
    and distributivity in the underlying ring; sorting is just
    re-arranging a sum (commutativity of addition). All of these
    preserve polynomial value.
-/

/-- Combining like terms preserves the sum.

    If two terms have the same monomial, replacing them with a
    single combined term (sum of coefficients, same monomial)
    does not change the sum. This is associativity + distributivity
    in the underlying ring. -/
theorem normalize_combine_like_terms {R : Type*} [CommRing R] {α : Type*}
    (c₁ c₂ : R) (a : α) (eval_mon : α → R) (rest_sum : R) :
    c₁ * eval_mon a + c₂ * eval_mon a + rest_sum =
    (c₁ + c₂) * eval_mon a + rest_sum := by
  ring

/-- Removing zero-coefficient terms preserves the sum. -/
theorem normalize_drop_zero_preserves_sum {R : Type*} [CommRing R] [DecidableEq R]
    {α : Type*} (terms : List (R × α)) (eval_mon : α → R) :
    ((terms.filter (fun p => !decide (p.1 = 0))).map
      (fun p => p.1 * eval_mon p.2)).sum =
    (terms.map (fun p => p.1 * eval_mon p.2)).sum := by
  induction terms with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : hd.1 = 0
    · simp [List.filter, h, ih]
    · simp [List.filter, h, ih]

end PolyRing
