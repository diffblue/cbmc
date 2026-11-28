\ingroup module_hidden

\page proof-explanation Proof Explanation

\author CBMC Contributors

# Proof Explanation: Word-Level Explanations for Proved Properties

## 1. Motivation

When CBMC proves that a property holds, it reports `VERIFICATION SUCCESSFUL`
but provides no further evidence or explanation. A counterexample trace explains
*why* a property is violated; proof explanations are the dual concept,
explaining *why* a property holds.

Users benefit from proof explanations in several ways:

- **Trust.** An explanation provides evidence that the proof is meaningful,
  not merely an artifact of modeling choices or bounds.
- **Understanding.** Developers can see which assignments, assumptions, and
  constraints in their code are responsible for the property holding.
- **Debugging unreachability.** When code is unreachable, a proof explanation
  for the unreachability query tells the user *why* the code cannot be reached.
- **Review.** In safety-critical development, reviewers can inspect the
  explanation alongside the verification result to gain confidence that the
  correct properties were checked against the correct code.

## 2. Background

CBMC performs bounded model checking by encoding a verification problem as a
Boolean satisfiability (SAT) formula. The formula is satisfiable if and only if
there exists an execution that violates the property. Therefore:

- **SAT** means the property can be violated. CBMC extracts a counterexample
  trace from the satisfying assignment.
- **UNSAT** means the property holds (it is impossible to violate within the
  given bounds). Traditionally, CBMC reports success and stops.

Modern SAT solvers can provide additional information on an UNSAT result.
In particular, they support **assumption-based conflict analysis**, which
identifies which of the assumptions passed to the solver participate in the
unsatisfiability proof:

- **CaDiCaL** exposes this via the `failed()` method. After an UNSAT result,
  calling `failed(literal)` returns true if the given literal (which must have
  been added as an assumption) is part of the conflict.
- **MiniSAT2** exposes this via the conflict clause. After an UNSAT result,
  the `conflict` member contains the set of assumption literals that form the
  unsatisfiable core.

Both mechanisms are already wired into CBMC through the `propt::is_in_conflict(literalt)`
virtual method, which is implemented by `satcheck_cadicalt` and
`satcheck_minisat2t`. At the word level, `prop_conv_solvert` wraps this as
`is_in_conflict(const exprt &)` via the `conflict_providert` interface.

## 3. CBMC Encoding Pipeline

The encoding pipeline transforms source code into a propositional formula
through several stages:

```
Source code
    |
    v
GOTO program (goto_modelt)
    |
    v
Symbolic Execution (goto_symext)
    |
    v
SSA equation (symex_target_equationt, containing SSA_stept entries)
    |
    v
Bit-vector encoding (boolbvt / prop_conv_solvert)
    |
    v
Propositional formula (CNF clauses)
    |
    v
SAT solver (CaDiCaL, MiniSAT2, etc.)
```

### Key mappings

- **`exprt` to `literalt`:** The `prop_conv_solvert` maintains a symbol-to-literal
  cache. When a word-level expression is converted, each bit of the result is
  mapped to a propositional literal. The `boolbv_mapt` stores this mapping:
  for each identifier, it records a `bvt` (vector of `literalt` values)
  representing the individual bits.

- **`literalt` to SAT variable:** Each `literalt` wraps a SAT variable number
  and a sign bit. The SAT solver operates on these variables directly.

- **SSA steps:** Each `SSA_stept` in the equation has a `guard_handle` and
  a `cond_handle`, both stored as `literal_exprt` values after conversion.
  The guard controls whether the step is active in a given execution path;
  the condition encodes the step's semantic content (e.g., the right-hand
  side of an assignment or the condition of an assumption).

## 4. Implementation

### Phase 1: SSA-step filtering (`--proof-explanation`)

The `--proof-explanation` command-line option enables proof explanations
for properties that CBMC proves to hold. The implementation lives in
`src/goto-checker/proof_explanation.h` and `src/goto-checker/proof_explanation.cpp`.

#### Algorithm

After the SAT solver returns UNSAT (all properties hold), the
`get_proof_explanation()` function iterates over the SSA steps in the
`symex_target_equationt` and collects steps that are relevant to the proof:

1. **Skip ignored steps.** Steps that were removed by the formula slicer
   (`--slice-formula`) have their `ignore` flag set. These are excluded.

2. **Filter by step type.** Only assignments, assumptions, and constraints
   are included. Assertions (the properties being proved), declarations,
   gotos, and other structural steps are excluded.

3. **Filter internal steps.** Steps originating from built-in initialization
   (source files matching `<built-in-*>` or `<builtin-*>`), internal SSA
   variables (identifiers containing `goto_symex::` or `return'`), and
   steps without useful source locations are excluded.

4. **Collect results.** Each surviving step produces a `proof_explanation_stept`
   containing:
   - `source_location`: the source file, line, and function
   - `step_type`: "assignment", "assumption", or "constraint"
   - `description`: a human-readable rendering of the step's content
   - `in_core`: whether the step is in the unsat core (see Phase 2)

### Phase 2: Assumption-based unsat core extraction

Phase 2 refines the proof explanation by using the SAT solver's
assumption-based conflict analysis to identify which steps are truly
part of the unsat core. The implementation is in
`get_proof_explanation_with_core()` in `proof_explanation.cpp`.

#### Algorithm

After the initial UNSAT solve, `get_proof_explanation_with_core()`:

1. **Collects candidate steps** using the same filtering as Phase 1.

2. **Gathers guard handles.** Each SSA step has a `guard_handle` that
   was set during `convert_guards()` via `decision_procedure.handle(guard)`.
   For steps with non-constant guards (branching), the guard handle is a
   `literal_exprt` wrapping the SAT literal for the guard. Steps with
   constant-true guards (straight-line code) are always active and are
   trivially marked as in the core.

3. **Pushes guard handles as SAT assumptions.** Using the
   `stack_decision_proceduret::push(vector<exprt>)` interface, the
   non-constant guard handles are added to the solver's assumption stack.
   This follows the same pattern used by `goto_symex_fault_localizert`.

4. **Re-solves.** The solver is called again. Since the formula already
   encodes all constraints and the guard assumptions only constrain
   additional paths to be active, the result should still be UNSAT.

5. **Checks conflict membership.** For each guard handle, the solver's
   `is_in_conflict()` method (from the `conflict_providert` interface)
   is called. This queries the SAT solver's `failed()` mechanism
   (CaDiCaL) or conflict clause (MiniSAT2) to determine whether
   the guard assumption participated in the UNSAT proof.

6. **Marks core membership.** Steps whose guards are in the conflict
   have `in_core=true`. Steps with constant-true guards are always
   marked as in the core. Steps whose guards are not in the conflict
   have `in_core=false`.

7. **Cleans up.** The assumption context is popped via `solver.pop()`.

The conflict provider is accessed via `dynamic_cast<conflict_providert*>`
on the `stack_decision_proceduret`. If the solver does not support the
`conflict_providert` interface (e.g., some SMT backends), all steps are
marked as in the core as a safe fallback.

#### Output

Each step is annotated with `[core]` in the plain-text output. Steps
not in the core are shown without the marker. For JSON output, an
`inCore` boolean field is added. For XML output, an `in-core` attribute
is set.

### Output format

The explanation is printed after `VERIFICATION SUCCESSFUL` in a section
headed by `Proof explanation:`. Steps in the unsat core are prefixed with
`[core]`. For JSON and XML output modes, structured `proof-explanation`
elements are emitted with core annotations (`inCore` for JSON,
`in-core` for XML), following the same pattern as fault localization
output. The formatting logic is in `output_proof_explanation()` in
`src/goto-checker/report_util.cpp`.

### Soundness

Phase 1 produces a **sound over-approximation**: every step that is
genuinely necessary for the proof will be reported, but some reported
steps may not actually be required. The slicer (`--slice-formula`)
already removes syntactically irrelevant steps before solving, so the
explanation only includes steps that survived slicing.

Phase 2 refines this using assumption-based conflict analysis on guard
handles. Steps whose guards are not in the UNSAT conflict are marked
`in_core=false`. For straight-line programs where all guards are
constant-true, all steps remain marked as in the core. For programs
with branching, steps on irrelevant branches may be identified as
not in the core.

### Integration point

The proof explanation is wired into the verification pipeline through the
`multi_path_symex_checkert`, which provides a `get_proof_explanation()` method.
The `stop_on_fail_verifier` and `all_properties_verifier_with_trace_storage`
templates call this method when `--proof-explanation` is enabled and the result
is PASS. A C++17 type trait (`has_get_proof_explanationt`) with `if constexpr`
is used to support checker types that do not provide proof explanations.

## 5. Examples

### 5.1 Simple assignment

```c
int main() {
  int x = 5;
  __CPROVER_assert(x > 0, "x is positive");
  return 0;
}
```

Running `cbmc --proof-explanation` reports:

```
Proof explanation:
  assignment: x = 5  (file main.c line 3)
```

The assignment `x = 5` is the key step that makes `x > 0` hold.

### 5.2 Branching

```c
int main() {
  int y = 10;
  int x;
  if(y > 5)
    x = 3;
  else
    x = -1;
  __CPROVER_assert(x > 0, "x is positive");
  return 0;
}
```

The proof explanation reports both `y = 10` and `x = 3`. The branch
`y > 5` evaluates to true (since `y` is 10), so the assignment `x = 3` is
taken, making `x > 0` hold. The `else` branch (`x = -1`) is irrelevant
and excluded by slicing.

### 5.3 Assumptions

```c
int main() {
  int input;
  __CPROVER_assume(input >= 0);
  __CPROVER_assume(input < 100);
  int result = input + 1;
  __CPROVER_assert(result > 0, "result is positive");
  return 0;
}
```

The proof explanation reports both assumptions (`input >= 0` and
`input < 100`) and the assignment `result = input + 1`. Together,
these constrain `result` to the range [1, 100], ensuring `result > 0`.

## 6. Limitations of the Current Approach

1. **Over-approximation, not minimal core.** The current implementation
   collects all non-ignored, non-internal SSA steps of relevant types.
   This is broader than a true unsat core: some reported steps may not
   participate in the minimal proof of unsatisfiability.

2. **SSA-level granularity.** The explanation operates at the level of
   SSA steps, not at the level of individual SAT clauses or bit-level
   constraints. Two steps that happen to share a variable may both be
   reported even if only one is truly necessary.

3. **Syntactic dependency, not semantic necessity.** The formula slicer
   removes steps that have no syntactic dependency on the property. But
   syntactic dependency is a necessary condition for semantic relevance,
   not a sufficient one. Some syntactically connected steps may be
   semantically irrelevant.

4. **No support for incremental/single-path checking.** Currently, proof
   explanations are only available with the multi-path symex checker.
   Single-path and incremental checkers do not yet expose the needed
   interface.

## 7. Future Work: Toward True Unsat Core Extraction

### 7.1 Clause-level unsat cores

A more precise approach would track individual CNF clauses through the
bit-vector encoding and map each clause back to the SSA step that
produced it. After solving, the SAT solver's proof trace reveals which
original clauses were used in the refutation.

CaDiCaL supports proof tracing via `connect_proof_tracer()` and
`trace_proof()`. From the proof trace, the set of original input clauses
used in the derivation of the empty clause can be extracted. Combined
with clause-to-SSA-step tracking in the `boolbvt` encoding layer, this
would yield a precise mapping from the unsat core to source-level steps.

### 7.2 Assumption-based approach (implemented in Phase 2)

Phase 2 implements a guard-handle-based variant of the assumption
approach. Instead of re-encoding with activation literals, it pushes
the existing guard handles as SAT assumptions and uses `is_in_conflict()`
to determine which are in the core. See Section 4 for details.

A more precise variant would re-encode the SSA equation with one
activation literal per step:

```
activation_lit_i => step_constraint_i
```

All activation literals are passed as assumptions to the solver. After
UNSAT, calling `failed()` (or inspecting the MiniSAT2 conflict clause)
on each activation literal reveals which steps are in the core. This
produces a true assumption-based unsat core at the cost of a modified
encoding. It does not require re-solving; the activation literals are
simply additional assumptions in the same solve call.

### 7.3 Lifting to word-level invariants (implemented in Phase 3)

Phase 3 implements an initial version of word-level invariant extraction.
Given the proof explanation steps marked as core (from Phase 2), the
`extract_proof_invariants()` function groups them by variable to produce
structured invariant summaries.

The algorithm works as follows:

1. Correlate explanation steps back to their SSA steps by replaying
   the same filtering logic (`is_relevant_proof_step()`).
2. For each core step that is an assignment, the key variable is the
   left-hand side. The description is added as a constraint on that
   variable.
3. For each core step that is an assumption or constraint, find all
   symbol expressions referenced in the condition. For each such
   symbol, add the condition as a constraint on that variable.
4. Group by variable name (stripped of SSA level suffixes) and produce
   one `proof_invariantt` per variable, with a clean display name
   (stripped of scope prefixes and renaming suffixes).

For example, from the core steps `input >= 0`, `input < 100`, and
`result = input + 1`, the output is:

```
Proof invariants:
  input: input >= 0, not(input >= 100)
  result: result = input + 1
```

This is a grouping-based approach rather than full invariant synthesis.
Future work may synthesize more abstract invariants (e.g., range
summaries like `input in [0, 100)`) or produce implications
(e.g., `input >= 0 AND input < 100 implies result > 0`).

The implementation lives in `extract_proof_invariants()` in
`src/goto-checker/proof_explanation.cpp`, with output formatting in
`output_proof_invariants()` in `src/goto-checker/report_util.cpp`.
The `proof_invariantt` struct is defined in
`src/goto-checker/proof_explanation.h`.

### 7.4 Integration with coverage analysis (implemented in Phase 4)

Unreachable code corresponds to an UNSAT reachability query: the formula
encoding "can execution reach this program point?" is unsatisfiable.
Proof explanations for such queries tell users *why* the code cannot be
reached, which is valuable for:

- **Coverage analysis:** Understanding why a test cannot cover a particular
  branch.
- **Dead code detection:** Explaining to developers why a code path is
  infeasible, helping them decide whether to remove it or fix the
  conditions guarding it.

Phase 4 integrates proof explanations with CBMC's coverage analysis.
When `--cover` is used alongside `--proof-explanation`, the
`cover_goals_verifier_with_trace_storaget` template now outputs proof
explanations for unreachable coverage goals (those with
`property_statust::PASS`, meaning the reachability query was UNSAT).

The integration follows the same `if constexpr` type trait pattern used
in `stop_on_fail_verifier.h` and
`all_properties_verifier_with_trace_storage.h`:
- `has_get_proof_explanationt` detects whether the checker supports
  proof explanations
- `has_get_proof_invariantst` detects whether the checker supports
  proof invariants

In coverage mode, the property status semantics are inverted relative
to normal verification: `FAIL` means the coverage goal was reached
(SATISFIED), while `PASS` means the goal is unreachable (the
reachability formula is UNSAT). The proof explanation is emitted only
when there are unreachable goals (`PASS` status), since those are the
cases where the UNSAT result can be explained.

### 7.5 SMT-level unsat cores (implemented in Phase 5)

When using SMT solvers (e.g., Z3 via the `--smt2` backend), the solver
natively supports unsat core extraction at the theory level. Phase 5
integrates this capability so that the existing Phase 2 assumption-based
proof explanation approach works transparently with SMT backends.

**Implementation approach.** Rather than using SMT `(get-unsat-core)` with
named assertions, Phase 5 uses `(get-unsat-assumptions)` with
`(check-sat-assuming ...)`. This reuses the same guard-handle-based
conflict analysis that Phase 2 uses for SAT solvers. The key changes:

1. `smt2_convt` gains a `produce_unsat_cores` flag. When true, the SMT2
   preamble includes `(set-option :produce-unsat-cores true)`.

2. `smt2_convt::write_footer()` emits `(get-unsat-assumptions)` after
   `(check-sat-assuming ...)` when unsat core production is enabled.

3. `smt2_dect` now inherits from `conflict_providert` and implements
   `is_in_conflict(const exprt &)`. After an UNSAT result from
   `check-sat-assuming`, `read_result()` parses the
   `(get-unsat-assumptions)` response and stores the failed assumption
   literal names. The `is_in_conflict()` method converts a `literal_exprt`
   to its SMT2 identifier name and checks whether it appears in the
   failed set.

4. `solver_factory.cpp` enables `produce_unsat_cores` on the SMT2 solver
   when `--proof-explanation` is active.

With these changes, `get_proof_explanation_with_core()` in
`proof_explanation.cpp` works without modification: the
`dynamic_cast<conflict_providert*>(&solver)` now succeeds for
`smt2_dect`, and the push/pop/is_in_conflict flow operates via the SMT
solver's native unsat-assumptions mechanism.

**Solver compatibility.** This approach requires SMT solvers that support
both `check-sat-assuming` and `get-unsat-assumptions`. Z3, CVC5, and
Bitwuzla all set `use_check_sat_assuming = true` in the CBMC SMT2
interface. Solvers that do not support `check-sat-assuming` (e.g., CVC3,
MathSAT, Yices) fall back to plain `(check-sat)` with assumptions as
assertions, and `get-unsat-assumptions` is not emitted; in this case the
Phase 2 code falls back to marking all steps as in_core=true.

## 8. Related Work

- **Error explanation (Kroening et al., STTT 2005).** This work computes
  error explanations for failing properties using Craig interpolation
  and similar techniques. Re-implementing this is listed in CBMC's
  `FEATURE_IDEAS.md`. Proof explanation is the dual problem: explaining
  why a property *holds* rather than why it *fails*.

- **Fault localization.** CBMC already includes fault localization for
  failing properties via `goto_symex_fault_localizert` in
  `src/goto-checker/goto_symex_fault_localizer.cpp`. Fault localization
  identifies which program locations are most likely responsible for a
  property violation. Proof explanation applies analogous reasoning to
  the UNSAT (passing) case.

- **Proof witnesses (GraphML format).** CBMC can produce correctness
  witnesses in the GraphML-based format defined by SV-COMP. These
  witnesses encode structural information (e.g., loop invariant
  locations) but do not explain *why* the property holds in terms of
  contributing program steps. Proof explanations complement witnesses
  by providing semantic content.

## 9. Files

| File | Purpose |
|------|---------|
| `src/goto-checker/proof_explanation.h` | `proof_explanation_stept` struct (with `in_core` field), `proof_invariantt` struct, `get_proof_explanation()`, `get_proof_explanation_with_core()`, `extract_proof_invariants()` declarations, `has_get_proof_explanationt` and `has_get_proof_invariantst` type traits |
| `src/goto-checker/proof_explanation.cpp` | Implementation of `get_proof_explanation()`, `get_proof_explanation_with_core()`, and `extract_proof_invariants()` |
| `src/goto-checker/goto_symex_property_decider.h` | `get_proof_explanation()` and `get_proof_invariants()` methods on the property decider |
| `src/goto-checker/goto_symex_property_decider.cpp` | Calls `get_proof_explanation_with_core()` and `extract_proof_invariants()` |
| `src/goto-checker/report_util.h` | Declarations of `output_proof_explanation()` and `output_proof_invariants()` |
| `src/goto-checker/report_util.cpp` | Plain (`[core]` markers), JSON (`inCore`), and XML (`in-core`) output for explanations; plain, JSON, and XML output for invariants |
| `src/goto-checker/multi_path_symex_checker.h` | `get_proof_explanation()` and `get_proof_invariants()` methods on the checker |
| `src/goto-checker/stop_on_fail_verifier.h` | Calls proof explanation and invariants in the PASS case |
| `src/goto-checker/all_properties_verifier_with_trace_storage.h` | Calls proof explanation and invariants for all proved properties |
| `src/goto-checker/cover_goals_verifier_with_trace_storage.h` | Calls proof explanation and invariants for unreachable coverage goals |
| `src/goto-checker/solver_factory.cpp` | Enables `produce_unsat_cores` on SMT2 solvers when `--proof-explanation` is active |
| `src/solvers/smt2/smt2_conv.h` | `produce_unsat_cores` flag for SMT-level unsat core extraction |
| `src/solvers/smt2/smt2_conv.cpp` | Emits `(set-option :produce-unsat-cores true)` and `(get-unsat-assumptions)` in the SMT2 output |
| `src/solvers/smt2/smt2_dec.h` | `smt2_dect` inherits from `conflict_providert`; `is_in_conflict()` declaration |
| `src/solvers/smt2/smt2_dec.cpp` | Parses `(get-unsat-assumptions)` response; implements `is_in_conflict()` for SMT-level conflict checking |
| `src/goto-checker/bmc_util.h` | `OPT_BMC` and `HELP_BMC` entries for `--proof-explanation` |
| `src/cbmc/cbmc_parse_options.h` | Includes `--proof-explanation` in `CBMC_OPTIONS` |
| `regression/cbmc/proof-explanation1/` | Regression test: basic proof explanation |
| `regression/cbmc/proof-explanation2/` | Regression test: unsat core `[core]` markers |
| `regression/cbmc/proof-explanation3/` | Regression test: word-level invariant extraction |
| `regression/cbmc/proof-explanation4/` | Regression test: coverage analysis integration |
| `regression/cbmc/proof-explanation5/` | Regression test: SMT-level unsat core (requires Z3, tagged `smt-backend`) |
