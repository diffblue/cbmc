# Plan: XOR Resolution in CaDiCaL's Conflict Analysis Loop

## Background

CaDiCaL's conflict analysis works as follows:

1. Start with conflict clause `reason = conflict`
2. Call `analyze_reason(uip, reason, open, ...)` which iterates over
   `reason`'s literals and calls `analyze_literal` for each
3. `analyze_literal(lit)`:
   - If `lit` is at level 0: skip (unit)
   - If `lit` is at current level: increment `open` (will be resolved later)
   - If `lit` is at lower level: add to `clause` (goes into learned clause)
   - Mark `lit` as `seen`
4. Walk trail backwards to find next `seen` literal at current level → `uip`
5. Decrement `open`. If `open > 0`: get `uip`'s reason, goto step 2
6. When `open == 0`: `uip` is the 1st UIP. Learned clause = `{-uip} ∪ clause`

Standard resolution at step 2: for each literal in the reason clause,
add it to the resolvent (via `analyze_literal`). Variables appear once
(due to `seen` flag).

## XOR Resolution Opportunity

When `uip`'s reason is a clause from an XOR constraint `x₁ ⊕ x₂ ⊕ x₃ = r`,
standard resolution adds x₂ and x₃ to the resolvent (assuming x₁ = uip).
But if x₂ or x₃ already appear in the resolvent (from a previous XOR),
standard resolution keeps both copies. XOR resolution would CANCEL them.

Example: resolvent has {a, b, c}, reason is XOR(b, d, e)=1 resolving on b.
- Standard: resolvent becomes {a, b, c, d, e} \ {b} = {a, c, d, e} (4 lits)
- XOR: resolvent becomes {a, c} ⊕ {d, e} = {a, c, d, e} (same here)
But if reason is XOR(b, c, d)=1:
- Standard: {a, b, c, d, e} \ {b} ∪ {c, d} = {a, c, d, e} (c,d already seen)
- XOR: {a, b, c} ⊕ {b, c, d} = {a, d} (b and c cancel!) → 2 lits

The cancellation is the key benefit.

## Implementation Options

### Option A: Parallel GF(2) Resolvent

Maintain a GF(2) bit-vector resolvent alongside the standard `clause` vector.
When resolving with an XOR reason, XOR the matrix row into the resolvent
instead of calling `analyze_reason`. At the end, the learned clause is
derived from the GF(2) resolvent (for XOR-resolved variables) combined
with the standard clause (for non-XOR variables).

**Pros**: Captures all XOR cancellations. Maximal benefit.
**Cons**: Complex interaction between GF(2) and standard resolution.
The `open` counter and `seen` flags must be kept consistent.

### Option B: XOR Reason Substitution

When `uip`'s reason is an XOR clause, replace it with a SHORTER reason
derived from the XOR matrix. The matrix row for `uip`'s variable, after
substituting assigned variables, gives an alternative reason. If this
reason has fewer literals at the current level, use it instead.

**Pros**: Minimal changes to analysis loop. Just replace `reason` pointer.
**Cons**: Doesn't capture cross-resolution cancellations. Only helps when
the XOR-derived reason is shorter than the clause reason.

### Option C: XOR-Aware Clause Minimization (deeper version)

After standard analysis, use the XOR matrix to remove redundant literals.
For each literal L in the learned clause, check if L can be derived from
other literals in the clause via XOR constraints. If so, L is redundant.

This is like CaDiCaL's existing minimization but using XOR implications
in addition to standard implications.

**Pros**: Safe (only removes literals, never adds). Compatible with all
CaDiCaL features.
**Cons**: Post-processing, so doesn't affect the `open` counter or UIP
selection. May miss opportunities that in-loop resolution would catch.

## Chosen Approach: All Three

Implement all three and benchmark. They are independent and can be
combined.

## Detailed Implementation Plan

### Step 1: Tag XOR clauses (shared infrastructure)

When adding derived clauses from Gaussian elimination, record which
CaDiCaL clauses came from which XOR matrix row. Use a map from
clause-id to matrix-row-index.

Implementation:
- In `satcheck_cadical.cpp`: after `solver->add(0)`, get the clause id
  and record the mapping
- In `GaussPropagator`: add `std::unordered_map<int64_t, int> clause_to_row`
- Problem: CaDiCaL doesn't expose clause ids after `add()`. Alternative:
  tag clauses by their literal set (hash the sorted literals).

Actually simpler: don't tag individual clauses. Instead, when we need to
know if a variable has an XOR reason, check `e_pivot[evar]`. If the
variable has a pivot row, its XOR reason is that row.

### Step 2: Option B — XOR Reason Substitution

In the analysis loop, when we get `reason = var(uip).reason`:
1. Convert `uip` to external variable `evar`
2. Check `gauss->has_pivot(evar)`
3. If yes, build a reason clause from the XOR row:
   - The row contains variables v₁, v₂, ..., vₙ with rhs
   - All except `evar` should be assigned
   - The reason clause is {uip, ~a₁, ~a₂, ...} where aᵢ are the
     assigned variables with their current values negated
4. If this reason is shorter than `var(uip).reason`, create a new
   clause and use it

Location: in `analyze()`, right after `reason = var(uip).reason` and
the `external_reason` check (around line 1180 in original).

### Step 3: Option A — Parallel GF(2) Resolvent

Maintain `std::vector<uint64_t> xor_resolvent` and `bool xor_rhs`.
In `analyze_reason`, when the reason is an XOR clause:
1. XOR the matrix row into `xor_resolvent`
2. For each variable in the XOR row:
   - If it's at the current level and in `xor_resolvent`: it's "open"
     in the XOR sense
   - If it's at a lower level and in `xor_resolvent`: it goes into
     the learned clause
   - If it WAS in `xor_resolvent` but got cancelled: it's removed
     from the learned clause (un-see it)
3. The `open` counter must account for XOR cancellations

This is the hardest to implement correctly because of the interaction
with `seen` flags and `open` counter.

### Step 4: Option C — XOR-Aware Minimization (improved)

After standard minimization, for each literal L in the learned clause:
1. Get L's external variable `evar`
2. If `gauss->has_pivot(evar)`:
   a. Get the XOR row R for `evar`
   b. For each other variable v in R:
      - If v is at level 0: skip (contributes nothing)
      - If v is in the learned clause: skip (already accounted for)
      - If v is NOT in the clause and NOT at level 0: L cannot be removed
   c. If all other variables are at level 0 or in the clause: remove L

This is what we tried before but it rarely fires because XOR rows are
ternary (3 variables). The improvement: also check if v can be
TRANSITIVELY derived via other XOR rows. Walk the XOR matrix to find
chains of implications.

## Execution Order

1. Implement Option B (simplest, most likely to help)
2. Benchmark
3. Implement Option C with transitive closure
4. Benchmark
5. Implement Option A if B+C don't provide sufficient speedup
6. Final benchmark with all combinations
