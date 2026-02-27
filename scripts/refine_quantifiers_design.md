# Design: `--refine-quantifiers` — Lazy Quantifier Instantiation

## Problem

CBMC's SAT backend eagerly instantiates every quantified formula over all
ground indices. For PQC proofs with 256-element polynomial arrays, this
creates millions of SAT clauses that dominate memory and solving time.

### Measurements (mldsa-native proofs)

| Proof | Unique ∀ | VCC ∀ | SAT vars | SAT clauses | Conv MB | Solve MB | Ratio |
|-------|----------|-------|----------|-------------|---------|----------|-------|
| poly_chknorm | 2 | 41 | 115K | 243K | 24 | 132 | 5.5× |
| poly_reduce | 4 | 43 | 2.4M | 11.4M | 27 | 4,817 | 178× |
| poly_add | 5 | 41 | 3.6M | 16.8M | ~30 | ~7,000 | ~230× |

Memory is overwhelmingly in the SAT solver's clause database, not in
CBMC's bitvector conversion (24–30 MB across all proofs).

### Root cause

Each `forall { k; k < 256 ==> body(coeffs[k]) }` generates 256 conjuncts.
A typical DFCC contract proof has ~40 quantifier occurrences across VCCs
(preconditions, postconditions, loop invariants, frame conditions). This
yields 40 × 256 = 10,240 ground instances, each encoding array accesses
and arithmetic into hundreds of SAT clauses.

Most of these instances are irrelevant to the proof. The SAT solver
ultimately needs only a small subset — typically the instances at the
loop index and boundary values.

## Proposed Solution

A CEGAR-based lazy instantiation loop, analogous to `--refine-arrays`:

```
1. Convert quantifiers to placeholder literals (no instantiation)
2. Solve the abstracted formula
3. If UNSAT → done (UNSAT)
4. If SAT → extract model, check each quantifier against model
5. For violated quantifiers, add instantiations for violating indices
6. Go to 2
```

### Key insight

For `forall { k; k < 256 ==> coeffs[k] < B }`, if the SAT model assigns
`coeffs[42] = 999` and `B = 100`, we only need to add the instance at
`k = 42`. The solver then either finds a different model or proves UNSAT.

## Architecture

### Integration point

The existing code already has the right structure:

```
boolbvt::convert_quantifier()
  → tries eager_quantifier_instantiation() (constant bounds)
  → falls back to quantifier_list (deferred to post-processing)

boolbvt::finish_eager_conversion_quantifiers()
  → calls instantiate_one_quantifier() for each deferred quantifier
  → generates ALL instantiations upfront
```

With `--refine-quantifiers`, `finish_eager_conversion_quantifiers()` would
instead:
1. Assign a fresh literal to each quantifier (already done)
2. Set `forall` literals to TRUE, `exists` literals to FALSE (abstraction)
3. Register quantifiers for refinement checking

Then the CEGAR loop in `bv_refinementt::dec_solve()` would check quantifiers
alongside array constraints.

### Class hierarchy

```
                    decision_proceduret
                           |
                       equalityt
                           |
                        arrayst
                           |
                       boolbvt          ← quantifier_list, bv_cache
                           |
                      bv_pointerst
                           |
                    bv_refinementt      ← CEGAR loop (arrays + arithmetic)
```

`bv_refinementt` already has the CEGAR loop. We add quantifier refinement
as a third refinement dimension alongside arrays and arithmetic.

### New code

**In `bv_refinementt`:**

```cpp
struct configt {
  bool refine_arrays = true;
  bool refine_arithmetic = true;
  bool refine_quantifiers = false;  // NEW
};
```

**New file `src/solvers/refinement/refine_quantifiers.cpp`:**

```cpp
void bv_refinementt::quantifiers_overapproximated()
{
  if(!config_.refine_quantifiers)
    return;

  // For each deferred quantifier with literal l:
  for(auto &q : quantifier_list)
  {
    auto &qexpr = to_quantifier_expr(q.expr);

    // Evaluate the quantifier body against the current SAT model.
    // For forall { k; k < N ==> body(k) }:
    //   Find a k in [0, N) where body(k) is false under the model.
    auto violating = find_violating_instance(qexpr);

    if(!violating.has_value())
      continue;  // quantifier satisfied by model

    // Add the violated instance as a new constraint
    exprt instance = qexpr.instantiate({*violating});
    if(qexpr.id() == ID_forall)
      prop.l_set_to_true(prop.limplies(q.l, convert(instance)));
    else
      prop.l_set_to_true(prop.limplies(convert(instance), q.l));

    progress = true;
  }
}
```

**Finding violating instances:**

```cpp
std::optional<exprt> bv_refinementt::find_violating_instance(
  const quantifier_exprt &q)
{
  // Extract bounds from the quantifier body (reuse eager logic)
  auto bounds = get_quantifier_bounds(q);
  if(!bounds)
    return {};

  // Iterate over the bound range, evaluate body under model
  for(mp_integer i = bounds->lb; i <= bounds->ub; ++i)
  {
    exprt val = from_integer(i, q.symbol().type());
    exprt instance = q.instantiate({val});
    exprt evaluated = get(instance);  // evaluate under SAT model

    if(q.id() == ID_forall && evaluated == false_exprt())
      return val;
    if(q.id() == ID_exists && evaluated == true_exprt())
      return val;  // not violating for exists
  }

  if(q.id() == ID_exists)
    return from_integer(bounds->lb, q.symbol().type());  // none satisfied

  return {};  // forall: all satisfied
}
```

### Integration into CEGAR loop

In `bv_refinementt::check_SAT()`:

```cpp
void bv_refinementt::check_SAT()
{
  progress = false;
  arrays_overapproximated();
  quantifiers_overapproximated();  // NEW
  // ... existing arithmetic refinement ...
}
```

### Freezing quantifier variables

Quantifier bodies reference array elements. For incremental solving, the
SAT variables for these elements must be frozen (not eliminated by
preprocessing). This is analogous to `freeze_lazy_constraints()` for arrays.

For the PQC proofs, the arrays are already materialized in the formula
(they appear in non-quantified constraints too), so their variables are
already present. We just need to freeze the quantifier placeholder literals.

## Correctness

### Soundness

- **UNSAT is sound**: If the abstracted formula (fewer constraints) is UNSAT,
  the full formula is also UNSAT.
- **SAT is sound**: We only report SAT when the model satisfies all quantifiers.
  The `find_violating_instance` check is exhaustive over the bound range.

### Completeness

- **Termination**: Each refinement iteration adds at least one new ground
  instance. The bound range is finite (256 for PQC proofs), so the loop
  terminates in at most 256 iterations per quantifier.
- **Worst case**: If all instances are needed, we converge to the eager
  instantiation. Performance is never worse than eager (modulo overhead of
  incremental solving).

### Comparison with `--refine-arrays`

| Aspect | `--refine-arrays` | `--refine-quantifiers` |
|--------|-------------------|------------------------|
| Abstraction | Drop array axioms | Drop quantifier instances |
| Check | Evaluate array constraints on model | Evaluate quantifier body on model |
| Refine | Add violated array axiom | Add violated quantifier instance |
| Termination | Finite (bounded by #indices × #arrays) | Finite (bounded by range × #quantifiers) |

## Expected Impact

For the 41 quantifier-heavy PQC proofs that currently timeout/OOM:

- **Best case**: Most proofs need only O(1) instances per quantifier (the
  loop index and boundaries). Formula shrinks from 10K+ instances to ~100.
  Memory drops from GBs to ~100MB. Solving time drops from timeout to seconds.

- **Typical case**: DFCC frame condition quantifiers (`unchanged(coeffs)`)
  may need all 256 instances since the solver must verify element-wise
  equality. But precondition/postcondition quantifiers (`array_bound`) likely
  need very few instances.

- **Worst case**: All instances needed → same as eager, plus incremental
  solving overhead (~10-20% slower).

## Measured Impact (prototype)

### Memory reduction
| Proof | Eager vars | Eager clauses | Eager MB | Refine vars | Refine MB | Reduction |
|-------|-----------|---------------|----------|-------------|-----------|-----------|
| poly_chknorm | 115K | 243K | 133 | 66K | 45 | 3.0× |
| poly_reduce | 2.4M | 11.4M | 4,817 | 174K | 206 | 23× |

### Key finding: all quantifiers are in assumptions
For DFCC contract proofs, ALL quantified formulas appear in VCC
assumptions (preconditions, loop invariant base cases, frame conditions).
ZERO appear in goals. This means:

1. The solver needs all instances to constrain the input — lazy
   instantiation converges to eager in the worst case.
2. The benefit comes from the SAT solver finding UNSAT proofs that
   don't need all quantifier implications, even though the bitvector
   encoding exists.
3. Memory savings are real (23× for poly_reduce) because the SAT
   solver's clause database is smaller without the implication clauses.

### Convergence
- Batch refinement: all violated instances are added per iteration.
- For field-sensitive arrays (≤64 elements): `get()` + `simplify_expr()`
  detects all violations in 1 iteration → 2 total iterations.
- For array-theory arrays (>64 elements): falls back to `convert()` +
  `l_get()` which adds the encoding but gives reliable evaluation.

### Solving time
The incremental SAT solving with frozen variables is slower than
non-incremental solving. CaDiCaL's preprocessing is less effective
with frozen variables. This is a known limitation of CEGAR approaches.

## Implementation Plan

1. Add `--refine-quantifiers` option and wire through `solver_factory.cpp`
2. In `finish_eager_conversion_quantifiers()`, skip instantiation when
   refinement is enabled; instead freeze placeholder literals
3. Add `quantifiers_overapproximated()` to `bv_refinementt::check_SAT()`
4. Implement `find_violating_instance()` using `get()` to evaluate under model
5. Add regression test with a quantifier-heavy proof
6. Benchmark on PQC proofs

Steps 1–4 are ~150 lines of new code.

## Open Questions

1. **Batch vs single instance**: Should we add all violating instances at once,
   or one per quantifier per iteration? Batch is faster convergence but adds
   more clauses per iteration.

2. **UNSAT refinement**: When the abstracted formula is UNSAT, the proof may
   use the quantifier placeholder literal. If the quantifier was
   over-approximated (set to TRUE for forall), UNSAT is sound. But if we
   want to support `--refine-quantifiers` with exists quantifiers in
   assumptions, we need under-approximation too.

3. **Interaction with `--refine-arrays`**: Both can be active simultaneously.
   The array refinement may add constraints that create new ground indices
   for quantifier instantiation. The current design handles this naturally
   since `find_violating_instance` evaluates against the current model.

4. **E-matching integration**: The current complete instantiation uses
   E-matching to find relevant indices. Could the refinement loop use
   E-matching on the model to find better instances? This is future work.
