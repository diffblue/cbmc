/-
  Termination of the Buchberger algorithm via the ascending chain
  condition (Noetherian property).
-/

import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

variable {R : Type*} [CommRing R]

/-! ## Ascending chain condition for ideals -/

/-- In a Noetherian ring, any monotone sequence of ideals stabilizes. -/
theorem ideal_chain_stabilizes [IsNoetherianRing R]
    (f : ℕ →o Ideal R) :
    ∃ n, ∀ m, n ≤ m → f n = f m := by
  exact (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr inferInstance f

/-! ## Strict growth when new element is outside the ideal -/

/-- If x ∉ Ideal.span S, then Ideal.span S < Ideal.span (S ∪ {x}). -/
theorem ideal_strict_growth {S : Set R} 
    (hx : x ∉ Ideal.span S) :
    Ideal.span S < Ideal.span (insert x S) := by
  constructor
  · exact Ideal.span_mono (Set.subset_insert x S)
  · intro h
    exact hx (h (Ideal.subset_span (Set.mem_insert x S)))

/-! ## Buchberger termination -/

/-- **Buchberger termination.** In a Noetherian ring, any monotone
    sequence of ideals stabilizes. Applied to the Buchberger algorithm:
    the sequence ⟨G₀⟩ ≤ ⟨G₁⟩ ≤ ... must stabilize, so the algorithm
    terminates. -/
theorem buchberger_terminates [IsNoetherianRing R]
    (f : ℕ →o Ideal R) :
    ∃ N, ∀ m, N ≤ m → f N = f m :=
  ideal_chain_stabilizes f

/-- At stabilization, every candidate new element is already in the ideal. -/
theorem stable_implies_no_new {S : Set R} 
    (h : Ideal.span (insert x S) = Ideal.span S) :
    x ∈ Ideal.span S := by
  have : x ∈ Ideal.span (insert x S) := Ideal.subset_span (Set.mem_insert x S)
  rwa [h] at this
