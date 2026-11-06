## Plan: Addressing Proof Explanation Limitations

### Limitation: Per-Property Explanations

**Current state:** The proof explanation covers all properties together.
When multiple properties hold, the explanation is the union of all
contributing steps.

**Goal:** Produce a separate explanation for each proved property.

**Approach:**

1. After the initial UNSAT result, iterate over each proved property.

2. For each property P, create a focused query: assert only P's negation
   (not all properties' negations). This isolates P's proof.

3. Use the solver's incremental interface (push/pop) to add P's negation
   as an assumption, solve, and extract the unsat core. Then pop and
   move to the next property.

4. The unsat core for each property gives a per-property explanation.

**Implementation sketch:**
```cpp
for(const auto &prop : proved_properties)
{
  solver.push({prop.negation_literal});
  auto result = solver();  // Should be UNSAT
  if(result == D_UNSATISFIABLE)
  {
    auto explanation = get_proof_explanation_with_core(equation, solver, ns);
    output_per_property_explanation(prop.id, explanation);
  }
  solver.pop();
}
```

**Complexity:** O(P × S) where P is the number of proved properties and
S is the solver time per query. Since each query reuses the existing
formula (just changing which property is negated), the solver can
leverage learned clauses and should be fast.

**Prerequisites:** The solver must support push/pop (MiniSAT with
simplifier disabled, CaDiCaL, or SMT solvers all support this).

### Limitation: Loop Invariant Synthesis

**Current state:** For loops, the explanation shows concrete unrolled
assignments (e.g., `x#3 = x#2 + 1`, `x#4 = x#3 + 1`, ...) rather
than a synthesized invariant (e.g., `x >= initial_x`).

**Goal:** Synthesize human-readable loop invariants from the unrolled
proof explanation.

**Approach (template-based):**

1. Identify groups of SSA steps that correspond to the same source
   location (same file/line) but different SSA versions. These are
   loop iterations.

2. For each group, extract the pattern. Common patterns:
   - Monotonic: `x#(i+1) = x#i + c` → invariant: `x >= x_init`
   - Bounded: `x#i < N` for all i → invariant: `x < N`
   - Constant: `x#i = c` for all i → invariant: `x = c`

3. Verify the candidate invariant against the unsat core: check that
   the invariant, together with the non-loop steps in the core,
   implies the property.

**Approach (Craig interpolation):**

1. Partition the formula into A (loop body) and B (everything else).
2. Compute the Craig interpolant I such that A ⇒ I and I ∧ B is UNSAT.
3. I is a loop invariant that's sufficient to prove the property.

This requires a solver that supports interpolation (e.g., MathSAT,
OpenSMT, or Z3 with interpolation enabled).

**Approach (abstract interpretation):**

1. Run CBMC's existing abstract interpretation (goto-analyzer) on the
   loop to compute an over-approximation of reachable states.
2. Intersect the abstract domain with the unsat core to produce a
   tighter invariant.
3. Report the intersection as the loop invariant.

**Recommended first step:** The template-based approach is simplest
and handles the most common cases (counters, bounds). It can be
implemented by post-processing the proof explanation output without
changing the solver interface.

**Implementation sketch for template-based approach:**
```cpp
// Group core steps by source location
std::map<source_locationt, std::vector<proof_explanation_stept>> by_location;
for(const auto &step : explanation)
  if(step.in_core)
    by_location[step.source_location].push_back(step);

// For locations with multiple steps (loop iterations), try templates
for(const auto &[loc, steps] : by_location)
{
  if(steps.size() > 1)
  {
    auto invariant = try_monotonic_template(steps);
    if(!invariant)
      invariant = try_bounded_template(steps);
    if(!invariant)
      invariant = try_constant_template(steps);
    if(invariant)
      report_loop_invariant(loc, *invariant);
  }
}
```
