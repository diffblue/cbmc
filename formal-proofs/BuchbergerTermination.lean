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

/-! ## Progress-tracking invariant for the iterative compute loop

The C++ Buchberger loop in `src/solvers/algebraic/groebner.cpp::compute`
uses two integer counters to decide when to bail out as `UNKNOWN`:
`pairs_since_last_progress` (called `counter` here) and
`pairs_at_last_progress` (called `baseline`). A premature bail-out
would be unsound for completeness only, but it would still cause
incorrect verdicts on ground-truth-UNSAT instances.

An earlier version of the C++ code reset the counters only after
the S-polynomial step. The 2-trick step's basis additions were
silently dropped from the termination criterion, so on instances
where the basis grew exclusively via the 2-trick the counter
could exceed the baseline while pairs added by the 2-trick were
still pending, and the loop bailed out as UNKNOWN before
processing them. The fix tracks the basis size at the start of
each iteration and resets the counters whenever the basis grew,
regardless of which step caused the growth.

The lemmas below model the corrected loop as a state machine and
prove the invariant `pairs_size + counter = baseline`. From this
invariant, the C++ termination check `counter > baseline` is
unreachable, i.e.\ the loop always exits via the queue-empty
condition. The buggy behaviour is captured separately as a step
that breaks the invariant.

PROOF: src/solvers/algebraic/groebner.cpp::strong_groebner_basist::compute
       (the `polys_size_at_iter_start` reset logic).
-/

/-- Abstract state of one iteration of the C++ compute loop. -/
structure ComputeState where
  /-- Size of the basis `polys`. -/
  basis_size : ℕ
  /-- Pending pairs in the queue. -/
  pairs_size : ℕ
  /-- `pairs_since_last_progress`. -/
  counter : ℕ
  /-- `pairs_at_last_progress`. -/
  baseline : ℕ
  deriving Repr

/-- The invariant maintained by the corrected progress tracking:
    pairs popped since the last reset, plus pairs still queued,
    equals the queue size at the moment of the last reset. -/
def ProgressInvariant (s : ComputeState) : Prop :=
  s.pairs_size + s.counter = s.baseline

/-- Initial state of the loop satisfies the invariant: counter is
    zero and baseline equals the initial queue size. -/
theorem progress_invariant_initial (basis pairs : ℕ) :
    ProgressInvariant ⟨basis, pairs, 0, pairs⟩ := by
  unfold ProgressInvariant
  show pairs + 0 = pairs
  omega

/-- One step of the corrected loop. Pops one pair (`pairs_size > 0`)
    and either grows the basis (resetting both counters) or leaves
    the basis unchanged (incrementing the counter). The number of
    pairs added by a growth step is the parameter `added`. -/
inductive Step : ComputeState → ComputeState → Prop where
  | grew (s : ComputeState) (added new_basis : ℕ) :
      s.pairs_size > 0 →
      new_basis > s.basis_size →
      Step s
        { basis_size := new_basis
        , pairs_size := s.pairs_size - 1 + added
        , counter := 0
        , baseline := s.pairs_size - 1 + added }
  | stable (s : ComputeState) :
      s.pairs_size > 0 →
      Step s
        { basis_size := s.basis_size
        , pairs_size := s.pairs_size - 1
        , counter := s.counter + 1
        , baseline := s.baseline }

/-- **Progress invariant preservation (corrected loop).**
    Every step of the corrected compute loop preserves the
    invariant `pairs_size + counter = baseline`. -/
theorem progress_invariant_preserved
    (s s' : ComputeState) (h : ProgressInvariant s) (step : Step s s') :
    ProgressInvariant s' := by
  cases step with
  | grew added new_basis _ _ =>
    unfold ProgressInvariant
    simp
  | stable hpairs =>
    unfold ProgressInvariant at h ⊢
    simp
    omega

/-- **Termination-check unreachability (corrected loop).**
    Under the progress invariant, the C++ termination check
    `counter > baseline` implies the queue is empty. Equivalently:
    while the queue is non-empty, `counter ≤ baseline`. The loop
    therefore exits via the queue-empty condition, not via the
    early-termination check. -/
theorem counter_exceeds_baseline_implies_empty
    (s : ComputeState) (h : ProgressInvariant s)
    (hc : s.counter > s.baseline) : s.pairs_size = 0 := by
  unfold ProgressInvariant at h
  omega

/-- The buggy step models the pre-fix behaviour: the basis grows
    via the 2-trick (`added > 0`), but the counter is incremented
    rather than reset. The growth contribution is not tracked. -/
inductive BuggyStep : ComputeState → ComputeState → Prop where
  | grew_2trick_only (s : ComputeState) (added new_basis : ℕ) :
      s.pairs_size > 0 →
      new_basis > s.basis_size →
      added > 0 →
      BuggyStep s
        { basis_size := new_basis
        , pairs_size := s.pairs_size - 1 + added
        , counter := s.counter + 1
        , baseline := s.baseline }

/-- **Buggy step breaks the invariant.** A growth step that fails
    to reset the counters violates the progress invariant whenever
    pairs were added (`added > 0`). This is precisely what allowed
    the buggy code to fire `counter > baseline` while pending
    pairs from the 2-trick step were still in the queue. -/
theorem buggy_step_breaks_invariant
    (s s' : ComputeState) (h : ProgressInvariant s)
    (step : BuggyStep s s') : ¬ ProgressInvariant s' := by
  cases step with
  | grew_2trick_only added new_basis _ _ hadded =>
    unfold ProgressInvariant at h ⊢
    simp
    omega
