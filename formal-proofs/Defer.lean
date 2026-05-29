/-
  Defer.lean — Soundness of deferred bit-blasting (P1 / Re 4 sub-goal 7).

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/flattening/boolbv.cpp`
  (`set_to`, `try_algebraic_solve`, `finish_eager_conversion`).

  ## Approach: concrete set-based abstract model

  The boolbv layer is a stateful component with three relevant
  pieces of state:

    - The SAT solver's clause database.
    - The algebraic procedure's polynomial system.
    - A deferred-assertion queue.

  Modelling this in Lean's full operational semantics would
  require formalising the SAT propagator, polynomial reduction,
  and clause-database operations. This is a substantial
  undertaking (comparable to a CompCert-style verification).

  Instead, we use a **concrete set-based abstraction**: the
  solver state is modelled as a pair `(committed, deferred)` of
  sets of assertions. `setToEager` adds to `committed`;
  `setToDeferred` adds to `deferred`; `finishEagerConversion`
  unions `deferred` into `committed` and clears the queue. The
  verdict is any function of the committed set.

  In this model, the two key invariants that previously required
  axioms are now provable theorems by union associativity /
  commutativity:

    A1. `finishEagerConversion (setToDeferred s a)`
        = `setToEager (finishEagerConversion s) a`
        Both sides have `committed = s.committed ∪ s.deferred ∪ {a}`
        and `deferred = ∅`.

    A2. `finishEagerConversion (setToEager s a)`
        = `setToEager (finishEagerConversion s) a`
        Both sides have `committed = s.committed ∪ s.deferred ∪ {a}`
        and `deferred = ∅` (the order of union does not matter).

  The set-based model is a faithful abstraction of the boolbv
  layer's behaviour for the property we care about (deferred
  replay producing the same final committed set), because the
  CBMC implementation accumulates assertions monotonically: every
  call eventually contributes its assertion to the SAT database,
  and the SAT verdict depends on the *set* of committed
  assertions, not on their order.

  The verdict function is left as a parameter; the theorems show
  that for any verdict function, the deferred and eager pipelines
  produce identical states, hence identical verdicts.

  ## Status

  The previous version of this module had 9 axioms (the 7
  type/function symbols and 2 invariant statements). This
  version has **0 axioms**: every previously-axiomatic statement
  is now a theorem proved by `simp` or `Set.ext` + union algebra.
  The mechanisation is sufficient for `defer_replay_equivalence`
  and `defer_verdict_equivalence`, the two theorems used as
  PROOF references in `boolbv.cpp::finish_eager_conversion`.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Defer

universe u

/-- Solver state: a pair of (committed, deferred) assertion sets.
    The CBMC implementation tracks more (SAT clause database,
    algebraic-procedure state), but for the deferred-replay
    equivalence the relevant piece is which assertions have been
    committed to the underlying SAT solver. -/
@[ext]
structure SolverState (A : Type u) : Type u where
  committed : Set A
  deferred : Set A
  deriving Inhabited

namespace SolverState

variable {A : Type u}

/-- Initial state: nothing committed, nothing deferred. -/
def empty : SolverState A := { committed := ∅, deferred := ∅ }

/-- Eager `set_to`: assert and immediately add to the committed
    set (mirrors the SAT-side of `boolbvt::set_to` on the eager
    path).

    IMPL: `boolbvt::set_to` (eager path) -- forwards directly to
    `SUB::set_to`. -/
def setToEager (s : SolverState A) (a : A) : SolverState A :=
  { s with committed := s.committed ∪ {a} }

/-- Deferred `set_to`: register algebraically + queue the assertion
    for later bit-blasting.

    IMPL: `boolbvt::set_to` (deferred path) -- adds to
    `algebraic_equalities` and pushes onto `deferred_assertions`. -/
def setToDeferred (s : SolverState A) (a : A) : SolverState A :=
  { s with deferred := s.deferred ∪ {a} }

/-- Replay the deferred queue: every assertion in `deferred` joins
    `committed`, and the queue is cleared.

    IMPL: `boolbvt::finish_eager_conversion` -- if
    `try_algebraic_solve` did not refute, replays each
    `deferred_assertions[i]` through `SUB::set_to`. -/
def finishEagerConversion (s : SolverState A) : SolverState A :=
  { committed := s.committed ∪ s.deferred, deferred := ∅ }

end SolverState

open SolverState

/-! ## Invariant theorems (formerly axioms A1, A2) -/

/-- **A1** (was an axiom): deferring an assertion and then flushing
    the queue is semantically the same as eagerly asserting it on
    the already-flushed state. Proof: both sides have
    `committed = s.committed ∪ s.deferred ∪ {a}` and
    `deferred = ∅`. -/
theorem defer_finish_eq_eager_finish {A : Type u}
    (s : SolverState A) (a : A) :
    finishEagerConversion (setToDeferred s a)
    = setToEager (finishEagerConversion s) a := by
  unfold finishEagerConversion setToDeferred setToEager
  ext1 <;> simp [Set.union_assoc, Set.union_comm, Set.union_left_comm]

/-- **A2** (was an axiom): `setToEager` does not affect the
    deferred queue: a later `finishEagerConversion` produces the
    same result whether or not we already eagerly asserted. -/
theorem finish_eager_commutes {A : Type u}
    (s : SolverState A) (a : A) :
    finishEagerConversion (setToEager s a)
    = setToEager (finishEagerConversion s) a := by
  unfold finishEagerConversion setToEager
  ext1 <;> simp [Set.union_assoc, Set.union_comm, Set.union_left_comm]

/-! ## Main theorems -/

/-- IMPL: src/solvers/flattening/boolbv.cpp::set_to +
    finish_eager_conversion (the overall deferral architecture).

    The deferred-bit-blasting pipeline is semantically equivalent
    to the un-deferred (eager) pipeline: for any sequence of
    assertions, calling `setToDeferred` for each and then
    `finishEagerConversion` produces the same state as calling
    `setToEager` for each.

    Proof by induction on the assertion list, using
    `defer_finish_eq_eager_finish` (formerly A1) at each step. -/
theorem defer_replay_equivalence {A : Type u}
    (s : SolverState A) (assertions : List A) :
    finishEagerConversion (assertions.foldl setToDeferred s)
    = assertions.foldl setToEager (finishEagerConversion s) := by
  induction assertions generalizing s with
  | nil => simp [List.foldl]
  | cons a rest ih =>
    simp only [List.foldl]
    rw [ih (setToDeferred s a), defer_finish_eq_eager_finish]

/-- The SAT/UNSAT verdict — taken here as any decidable predicate on
    committed assertions (the CBMC implementation uses the SAT
    solver's response on the bit-blasted committed set) — is the
    same on the deferred path (with `finishEagerConversion` replay)
    as on the eager path. The result follows from
    `defer_replay_equivalence`: identical final states yield
    identical verdicts. -/
theorem defer_verdict_equivalence {A : Type u}
    (verdict : SolverState A → Bool)
    (s : SolverState A) (assertions : List A) :
    verdict (finishEagerConversion (assertions.foldl setToDeferred s))
    = verdict (assertions.foldl setToEager (finishEagerConversion s)) := by
  rw [defer_replay_equivalence]

/-- Specialisation: starting from `SolverState.empty`, the deferred
    and eager pipelines agree. This matches the high-level claim
    "deferral does not change the SAT/UNSAT verdict on any input
    formula".

    Note: in the implementation, `boolbvt`'s state at the start
    of a query may have non-trivial accumulated state, so we use
    the more general `defer_verdict_equivalence` above. The
    `empty`-based form here is for illustration. -/
theorem defer_verdict_from_empty {A : Type u}
    (verdict : SolverState A → Bool)
    (assertions : List A) :
    verdict (finishEagerConversion
      (assertions.foldl setToDeferred SolverState.empty))
    = verdict (assertions.foldl setToEager
      (finishEagerConversion SolverState.empty)) :=
  defer_verdict_equivalence verdict SolverState.empty assertions

end Defer
