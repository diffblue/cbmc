/// \file
/// Branch Pruning
///
/// # Overview
///
/// CBMC's branch pruning queries a SAT solver at each `goto` branch point to
/// determine whether the guard (or its negation) is implied by the path
/// condition accumulated so far. If one direction is infeasible, that branch
/// is skipped, avoiding the exponential path explosion that would otherwise
/// arise from exploring branches that no execution can ever reach.
///
/// Branch pruning is enabled by default and operates in two modes:
///
/// - `--paths` (single-path symbolic execution): at each branch point with
///   a symbolic guard, the equation accumulated for the current path is
///   converted into a dedicated SAT solver inside a push/pop scope and the
///   feasibility of each direction is checked. Only the feasible branches
///   are added to the worklist.
///
/// - Monolithic (default): at each branch point, the SSA equation is
///   *incrementally* asserted into a long-lived shared SAT solver, and the
///   guards of the fall-through and jump-target successor states are
///   probed for satisfiability. Infeasible successors are marked
///   `reachable = false` so that symex skips them rather than constructing
///   useless SSA for unreachable code.
///
/// This is the same overall approach used by Soteria-C, which resolves
/// 99.9% of branches without forking on typical programs.
///
/// # Architecture
///
/// ## Solver Lifecycle
///
/// A dedicated SAT solver (`branch_worklist_solver`) is created in either
/// `single_path_symex_only_checkert` or `multi_path_symex_only_checkert`
/// for branch pruning. It is separate from the per-path property-checking
/// solver, and uses `satcheck_minisat_no_simplifiert` (where MiniSat is
/// available) to avoid `backwardSubsumptionCheck` overhead; in builds
/// without MiniSat, it falls back to `solver_factoryt::get_solver()`.
///
/// The solver is created once in the checker's constructor and reused for
/// the lifetime of the checker.
///
/// ## Branch Check Protocol -- `--paths` mode
///
/// In `symex_goto()`, when `doing_path_exploration` and the guard is symbolic:
///
/// 1. **Push** an outer solver scope to contain the equation assertions
/// 2. **Re-assert** the entire equation directly into the pruning solver
///    (own loop -- no `convert_without_assertions`):
///    - assignments and constraints as `cond_expr`
///    - assumes as `guard => cond_expr` (the equation conversion does
///      not assert assumes at top level)
///    The pruning solver is independent of the property-checking
///    solver, and we deliberately do not touch `step.converted`; the
///    property solver later runs its own incremental conversion.
/// 3. **Build a path-condition handle** from `state.guard.as_expr()`.
///    This is pushed alongside the branch guard in steps 4-5 so the
///    SAT solver cannot satisfy the branch by setting earlier guards
///    false (which would vacuously satisfy the equation regardless of
///    the actual current path).
/// 4. **Check guard feasibility**: push `path_handle && guard_handle`,
///    solve, pop
/// 5. **Check negation feasibility**: push `path_handle && ¬guard_handle`,
///    solve, pop
/// 6. **Pop** the outer equation scope so the solver state is back to
///    a clean slate before the next branch check
///
/// If the guard is infeasible, only the negation branch is taken.
/// If the negation is infeasible, only the guard branch is taken.
/// If both are feasible, normal forking proceeds.
///
/// ## Branch Check Protocol -- monolithic mode
///
/// In `symex_goto()`, when `!doing_path_exploration` and the goto is at a
/// non-saved-jump-target instruction outside an atomic section:
///
/// 1. **Incrementally convert** any new SSA steps that have not yet been
///    seen by the pruning solver, marking them via the per-step flag
///    `converted_for_pruning`. Assignments and constraints are asserted
///    unconditionally as `cond_expr`; assumes as `guard => cond_expr`.
///    Steps already marked `converted_for_pruning` are skipped.
/// 2. **Push** the fall-through state's `state.guard.as_expr()`, solve,
///    and pop. If UNSAT, mark `state.reachable = false`.
/// 3. **Push** the jump-target state's `guard.as_expr()`, solve, and pop.
///    If UNSAT, mark that successor's `reachable = false`.
///
/// Unlike `--paths` mode, the monolithic protocol never resets the
/// pruning-conversion flag: the equation grows monotonically as symex
/// progresses, so we want each step to be asserted into the pruning solver
/// exactly once. The property-checking solver continues to use the
/// independent `step.converted` flag for its own incremental conversion.
///
/// ## Assume Assertion
///
/// The key insight (in either mode): `convert_without_assertions()` calls
/// `handle()` on assume conditions but does not assert them into the
/// solver. Without explicit assertion, the solver cannot use
/// `__CPROVER_assume` constraints to resolve branches.
///
/// We assert each assume as `implies_exprt{step.guard, step.cond_expr}`.
/// The guard is included because in both modes, assumes inside conditional
/// code have non-trivial guards. Using `guard => cond` is always sound:
/// - If guard is true: the assume constrains the solver (correct)
/// - If guard is false: the implication is vacuously true (no effect)
///
/// # Adaptive auto-disable
///
/// Two complementary mechanisms keep the cost of pruning bounded
/// even when individual SAT calls go pathological:
///
///   * **Per-check budget.** Before each pruning solve the code
///     calls `set_time_limit_milliseconds(200)` on the pruning
///     solver (when the underlying back-end is a
///     `solver_resource_limitst`). Back-ends that natively support
///     a time limit -- MiniSat 2 (via a `std::thread` watchdog),
///     IPASIR (via `ipasir_set_terminate`), CaDiCaL (via the
///     `Terminator` callback) -- abort the SAT call if the budget
///     is exceeded and return `D_ERROR`. The pruning code treats
///     `D_ERROR` as "branch is feasible by default" (so soundness
///     is preserved) and disables further pruning for the rest of
///     the run.
///
///   * **Cumulative budget.** As a backstop for back-ends that
///     don't honour the per-check budget natively, each branch
///     check is timed and added to a `cumulative_pruning_ms`
///     counter on `goto_symext`. Once the cumulative pruning time
///     exceeds 1000 ms in a single run, pruning is auto-disabled
///     for the remainder of the run via
///     `branch_pruning_disabled = true`.
///
/// The combination guarantees that, on a back-end with native
/// timeout support, pruning's contribution to symex runtime is
/// bounded near 200-400 ms per run regardless of program shape.
/// Without native support the bound is 1 s plus the duration of
/// the slow check that triggered auto-disable.
///
/// # Disabling pruning
///
/// Pass `--no-branch-pruning` on the command line to disable branch
/// pruning entirely.
///
/// # Limitations
///
/// ## Refinement Solvers
///
/// Branch pruning is disabled when `--refine`, `--refine-arrays`, or
/// `--refine-strings` is used. These modes create a `bv_refinementt` solver
/// that uses iterative refinement. The branch pruning solver performs a single
/// SAT check without refinement, which can give unsound results on the initial
/// over-approximation (e.g., incorrectly determining a branch is infeasible).
///
/// ## Push/Pop Overhead (`--paths` mode)
///
/// Each branch check converts the entire equation inside a push/pop scope.
/// This is O(N) per check where N is the equation size. On programs with many
/// branches but no prunable constraints (e.g., Multi_Dimensional_Array6), this
/// adds ~15-20% overhead.
///
/// An incremental approach (keeping the equation in the solver across checks)
/// would reduce this to O(delta) per check, but requires careful handling of
/// MiniSat's variable elimination (use `set_all_frozen()`) and cross-path
/// constraint pollution (create a fresh solver per path). The monolithic
/// mode already uses incremental assertion via `converted_for_pruning`.
///
/// ## Variable Freezing
///
/// The solver uses `set_all_frozen()` to prevent MiniSat's `SimpSolver` from
/// eliminating variables during `solve()`. Without freezing, subsequent
/// `handle()` calls may reference eliminated variables, causing assertion
/// failures.
