/-
  ExtractCandidate.lean — Soundness of model extraction in
  `src/solvers/algebraic/groebner.cpp::extract_candidate`.

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  The `extract_candidate` function builds a candidate assignment
  by repeatedly solving univariate linear equations from the
  basis. After substituting known values, if a polynomial
  reduces to `c * x + d = 0` over `ZMod (2^bw)`, the function
  attempts to solve for `x`.

  Contract: when the function assigns a value to a variable,
  the polynomial that triggered the assignment evaluates to 0
  at that value (under the prior partial assignment).

  This module proves the local "univariate linear solve" fact,
  which is the core of `extract_candidate`'s soundness.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PolyRing

namespace ExtractCandidate

/-! ## Solving `c * x + d = 0` over `ZMod (2^bw)`

    Given a univariate linear equation `c * x + d = 0` in
    `ZMod (2^bw)`:
      - Let `v_c = ν₂(c)`, the 2-adic valuation of c. Write
        `c = 2^v_c * u` with `u` odd.
      - The equation has a solution iff `2^v_c ∣ d`. (Necessity:
        modulo 2^v_c, the equation reduces to `d ≡ 0`. Sufficiency:
        write `d = 2^v_c * d'`, then `x = -d' * u⁻¹` solves it
        mod `2^(bw - v_c)`, which is enough mod `2^bw`.)
-/

/-- The local "univariate linear solve" fact, simplified form.
    If `u` is odd (a unit in ZMod (2^bw)), then for any `d`,
    `x = -d * u⁻¹` solves `u * x + d = 0`. -/
theorem solve_univariate_linear_unit {bw : ℕ} (hbw : 0 < bw)
    {u : ℕ} (hu : ¬ 2 ∣ u) (d : ZMod (2 ^ bw)) :
    ∃ x : ZMod (2 ^ bw), (u : ZMod (2 ^ bw)) * x + d = 0 := by
  -- u is a unit; pick x = -(d * u⁻¹).
  obtain ⟨inv, h_inv⟩ := PolyRing.inverse_mod_2d_exists hbw hu
  refine ⟨-(d * inv), ?_⟩
  have : (u : ZMod (2 ^ bw)) * (-(d * inv)) + d
       = -((u : ZMod (2 ^ bw)) * inv * d) + d := by ring
  rw [this]
  -- (u : ZMod) * inv = 1 by h_inv
  rw [show (u : ZMod (2 ^ bw)) * inv = 1 from h_inv]
  ring

/-- General form: `c * x + d = 0` has a solution iff
    every "obstruction" coming from the 2-adic structure of `c`
    is also satisfied by `d`. The simplest sufficient condition:
    if `c` is itself a unit (odd in `ZMod (2^bw)`), there's always
    a unique solution.

    The C++ algorithm handles the general case by extracting the
    common factor 2^v_c from both sides and solving in
    `ZMod (2^(bw - v_c))`. We state the simpler unit case here;
    the general case reduces to it.

    Soundness consequence: when `extract_candidate` assigns a
    value to variable `x`, that value is constructed precisely
    so that `c * x + d = 0`. -/
theorem extract_candidate_local_soundness {bw : ℕ} (_hbw : 0 < bw)
    {c : ZMod (2 ^ bw)} (hc_unit : IsUnit c) (d : ZMod (2 ^ bw)) :
    ∃! x : ZMod (2 ^ bw), c * x + d = 0 := by
  -- Existence: x = -d * c⁻¹.
  -- Uniqueness: if c*x₁ + d = 0 = c*x₂ + d, then c*(x₁ - x₂) = 0,
  -- and since c is a unit, x₁ = x₂.
  obtain ⟨u, hu⟩ := hc_unit
  refine ⟨-(d * u.inv), ?_, ?_⟩
  · -- c * (-(d * u.inv)) + d = -(c * u.inv * d) + d = -d + d = 0
    have h_inv : c * u.inv = 1 := by
      rw [← hu]; exact u.val_inv
    calc c * -(d * u.inv) + d
        = -(c * u.inv * d) + d := by ring
      _ = -(1 * d) + d := by rw [h_inv]
      _ = 0 := by ring
  · -- Uniqueness
    intro y hy
    have h_inv : c * u.inv = 1 := by
      rw [← hu]; exact u.val_inv
    have h_inv' : u.inv * c = 1 := by
      rw [mul_comm]; exact h_inv
    -- c*y + d = 0 ⇒ c*y = -d ⇒ y = -d * u.inv (multiply by u.inv)
    have h1 : c * y = -d := by
      have := hy
      linear_combination this
    have h2 : u.inv * (c * y) = u.inv * (-d) := by rw [h1]
    rw [← mul_assoc, h_inv', one_mul] at h2
    rw [h2]; ring

end ExtractCandidate
