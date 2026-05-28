/-
  Defer.lean — Soundness of deferred bit-blasting (P1 / Re 4 sub-goal 7).

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/flattening/boolbv.cpp`
  (`set_to`, `try_algebraic_solve`, `finish_eager_conversion`).

  ## Approach: axiomatic semantic model

  The boolbv layer is a stateful component with three relevant
  pieces of state:

    - The SAT solver's clause database.
    - The algebraic procedure's polynomial system.
    - A deferred-assertion queue.

  Modelling this in Lean's full operational semantics would
  require formalising the SAT propagator, polynomial reduction,
  and clause-database operations. This is a substantial
  undertaking (comparable to a CompCert-style verification).

  Instead, we use an **axiomatic model**: we declare opaque types
  for the relevant semantic objects and postulate axioms that
  capture the invariants the implementation maintains. We then
  prove the deferred-replay equivalence as a theorem relative to
  those axioms.

  The axioms reflect properties an inspection of the code
  confirms:

    A1. `finishEagerConversion (setToDeferred s a)`
        = `setToEager (finishEagerConversion s) a`

        Deferring an assertion and then flushing the queue is
        semantically the same as eagerly asserting it on the
        already-flushed state. This is the **key** axiom.
        Justification: `finishEagerConversion` replays each
        queued assertion through the same `SUB::set_to` path
        that `setToEager` invokes; the algebraic state is
        accumulated in `setToDeferred` and `setToEager` the
        same way (both call `setToAlgebraic`).

    A2. `setToEager` does not change the deferred queue.

        After `setToEager s a`, the deferred queue is whatever
        it was in `s`.  We capture this via:
        `finishEagerConversion (setToEager s a)`
        = `setToEager (finishEagerConversion s) a`.

  From A1 and A2 we prove:

    `defer_replay_equivalence`:
        For any sequence of assertions, the deferred pipeline
        followed by `finishEagerConversion` produces the same
        final state as the eager pipeline applied directly.

  This in turn implies the SAT/UNSAT verdict is the same.

  ## Status

  This axiomatic formulation captures **what needs to hold** for
  the deferred-bit-blasting optimisation to be sound. A full
  mechanisation would either:

    (i)  Prove the axioms relative to a Lean model of the boolbv
         layer's operational semantics — out of scope for this
         project.

    (ii) Prove the axioms by code inspection plus a small
         operational-semantics formalisation. This is the
         realistic path; it would be a follow-on of perhaps
         1–2 weeks of focused Lean work.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Defer

/-- Abstract assertion type representing an SSA equality. -/
axiom Assertion : Type

/-- Abstract solver state (the conjunction of SAT clause database,
    algebraic-procedure state, and deferred queue). -/
axiom SolverState : Type

/-- Eager set_to: assert and immediately bit-blast.

    IMPL: `boolbvt::set_to` (eager path) -- forwards directly to
    `SUB::set_to`. -/
axiom setToEager : SolverState → Assertion → SolverState

/-- Deferred set_to: register algebraically + queue the assertion
    for later bit-blasting.

    IMPL: `boolbvt::set_to` (deferred path) -- adds to
    `algebraic_equalities` and pushes onto `deferred_assertions`. -/
axiom setToDeferred : SolverState → Assertion → SolverState

/-- Replay the deferred queue (or discard it on refutation).

    IMPL: `boolbvt::finish_eager_conversion` -- if
    `try_algebraic_solve` did not refute, replays each
    `deferred_assertions[i]` through `SUB::set_to`. -/
axiom finishEagerConversion : SolverState → SolverState

/-- Verdict: SAT (true) or UNSAT (false). -/
axiom verdict : SolverState → Bool

/-- Initial state. -/
axiom emptyState : SolverState

/-! ## Axioms reflecting the boolbv layer semantics -/

/-- **A1**: deferring an assertion and then flushing the queue is
    semantically the same as eagerly asserting it on the
    already-flushed state.

    Justification by code inspection: `finish_eager_conversion`
    calls `SUB::set_to` for each queued assertion, which is the
    same call that `setToEager` issues. The algebraic state is
    accumulated identically by `setToDeferred` and `setToEager`. -/
axiom defer_finish_eq_eager_finish :
    ∀ (s : SolverState) (a : Assertion),
      finishEagerConversion (setToDeferred s a)
      = setToEager (finishEagerConversion s) a

/-- **A2**: `setToEager` does not affect the deferred queue: a later
    `finishEagerConversion` produces the same result whether or
    not we already eagerly asserted.

    Justification by code inspection: `setToEager` does not push
    onto `deferred_assertions`; only `setToDeferred` does. -/
axiom finish_eager_commutes :
    ∀ (s : SolverState) (a : Assertion),
      finishEagerConversion (setToEager s a)
      = setToEager (finishEagerConversion s) a

/-! ## Main theorems -/

/-- IMPL: src/solvers/flattening/boolbv.cpp::set_to +
    finish_eager_conversion (the overall deferral architecture).

    The deferred-bit-blasting pipeline is semantically equivalent
    to the un-deferred (eager) pipeline: for any sequence of
    assertions, calling `setToDeferred` for each and then
    `finishEagerConversion` produces the same state as calling
    `setToEager` for each.

    Proof by induction on the assertion list, using axiom A1
    (defer_finish_eq_eager_finish) at each step. -/
theorem defer_replay_equivalence :
    ∀ (s : SolverState) (assertions : List Assertion),
      finishEagerConversion (assertions.foldl setToDeferred s)
      = assertions.foldl setToEager (finishEagerConversion s)
  | s, [] => by simp [List.foldl]
  | s, a :: rest => by
    -- LHS = finishEagerConversion (rest.foldl setToDeferred (setToDeferred s a))
    --     = rest.foldl setToEager (finishEagerConversion (setToDeferred s a))   [IH]
    --     = rest.foldl setToEager (setToEager (finishEagerConversion s) a)      [A1]
    -- RHS = (a :: rest).foldl setToEager (finishEagerConversion s)
    --     = rest.foldl setToEager (setToEager (finishEagerConversion s) a)
    simp only [List.foldl]
    rw [defer_replay_equivalence (setToDeferred s a) rest,
        defer_finish_eq_eager_finish]

/-- The SAT/UNSAT verdict is the same on the deferred path
    (with finishEagerConversion replay) as on the eager path. -/
theorem defer_verdict_equivalence (s : SolverState) (assertions : List Assertion) :
    verdict (finishEagerConversion (assertions.foldl setToDeferred s))
    = verdict (assertions.foldl setToEager (finishEagerConversion s)) := by
  rw [defer_replay_equivalence]

/-- Specialisation: starting from `emptyState` (clean state), the
    deferred and eager pipelines agree. This matches the
    high-level claim "deferral does not change the SAT/UNSAT
    verdict on any input formula".

    Note: in the implementation, `boolbvt`'s state at the start
    of a query may have non-trivial accumulated state, so we use
    the more general `defer_verdict_equivalence` above. The
    `emptyState`-based form here is for illustration. -/
theorem defer_verdict_from_empty (assertions : List Assertion) :
    verdict (finishEagerConversion (assertions.foldl setToDeferred emptyState))
    = verdict (assertions.foldl setToEager (finishEagerConversion emptyState)) :=
  defer_verdict_equivalence emptyState assertions

end Defer
