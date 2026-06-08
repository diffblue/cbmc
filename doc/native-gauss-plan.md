# Plan: Native Gaussian Elimination in CaDiCaL

## Background

The ExternalPropagator approach works correctly but has a fixed 2.4s
overhead from CaDiCaL's callback framework (`notify_assignment`,
`cb_propagate`, `cb_has_external_clause` called on every CDCL
iteration). Native integration eliminates this overhead entirely.

Our prototype native integration showed 45-960x speedups but had a
correctness bug: setting `elimxors=0` to prevent CaDiCaL from
eliminating XOR variables changed CaDiCaL's preprocessing behavior,
causing wrong results on some formulas.

## Architecture

CaDiCaL's reason clause mechanism has two paths:

1. **Normal reasons**: `var.reason = Clause*` — a pointer to an
   existing clause in the clause database. Used by BCP.

2. **External reasons**: `var.reason = external_reason` — a sentinel
   pointer. When conflict analysis encounters this, it calls
   `learn_external_reason_clause()` which materializes the reason
   lazily via the ExternalPropagator callback.

The key insight: we can add a **third path** — `gauss_reason` — that
works like `external_reason` but materializes reasons from the Gauss
matrix directly, without the ExternalPropagator callback overhead.

## Detailed Plan

### Phase 1: Gauss reason sentinel (CaDiCaL patch)

**Files to modify**: `internal.hpp`, `analyze.cpp`, `collect.cpp`

1. Add a `gauss_reason` sentinel (like `external_reason`):
   ```cpp
   // internal.hpp
   static Clause gauss_reason_clause;
   Clause *gauss_reason = &gauss_reason_clause;
   ```

2. In `analyze.cpp`, handle `gauss_reason` alongside `external_reason`:
   ```cpp
   if (v.reason == gauss_reason) {
     v.reason = learn_gauss_reason_clause(-lit);
     if (!v.reason) { /* unit */ }
   }
   ```
   This is ~10 lines, mirroring the existing `external_reason` handling.

3. In `collect.cpp`, protect `gauss_reason` from GC (same as
   `external_reason` — ~3 lines).

4. In `backtrack.cpp`, handle `gauss_reason` in chronological
   backtracking (same as `external_reason` — ~2 lines).

**Effort**: ~30 lines of CaDiCaL changes.

### Phase 2: Gauss propagator integration (CaDiCaL patch)

**Files to modify**: `internal.hpp`, `propagate.cpp`, `backtrack.cpp`,
`decide.cpp`

1. Add `GaussPropagator*` member to `Internal` (already done in
   prototype).

2. In `propagate()` (the BCP hot loop), after processing each literal
   from the trail, notify the Gauss matrix:
   ```cpp
   // At the END of the while loop body, after all watched clauses processed:
   if (gauss && gauss->has_var(evar))
     gauss->assign(evar, lit > 0);
   ```
   This is inside the BCP loop but only fires for variables in the
   Gauss matrix (~15K out of ~50K total). The `has_var` check is O(1).

3. After the BCP loop completes (before `STOP(propagate)`), check for
   Gauss propagations:
   ```cpp
   while (gauss && !conflict) {
     int glit = gauss->propagate();
     if (!glit) break;
     int ilit = e2i(glit);
     if (ilit && !val(ilit)) {
       search_assign(ilit, gauss_reason);
       // Continue BCP for the new assignment
       // (re-enter the main BCP loop)
     }
   }
   ```
   The `search_assign(ilit, gauss_reason)` sets the reason to our
   sentinel. No clause is created. When conflict analysis needs the
   reason, it calls `learn_gauss_reason_clause` (Phase 1).

4. In `backtrack.cpp`, backtrack the Gauss matrix using trail-size
   tracking (already done in prototype).

**Effort**: ~50 lines of CaDiCaL changes.

### Phase 3: Lazy reason materialization (CaDiCaL patch)

**Files to modify**: `internal.hpp`, a new `gauss_reason.cpp`

1. Implement `learn_gauss_reason_clause(int ilit)`:
   ```cpp
   Clause* Internal::learn_gauss_reason_clause(int ilit) {
     int elit = externalize(ilit);
     auto reason = gauss->get_reason(abs(elit));
     // Convert DIMACS reason to internal clause
     clause.clear();
     for (int el : reason) {
       int il = e2i(el);
       if (il) clause.push_back(il);
     }
     if (clause.size() <= 1) return nullptr; // unit
     // Sort: propagated literal first, highest level at position 1
     // ... (same as new_clause setup)
     Clause *c = new_clause(true, 1);
     watch_clause(c);
     return c;
   }
   ```

2. The Gauss matrix's `get_reason` must return the ORIGINAL XOR
   variables (not the reduced matrix row). This requires the
   `row_to_xor` mapping from the prototype.

**Effort**: ~40 lines.

### Phase 4: Variable elimination compatibility

**The core problem**: CaDiCaL's BVE (`elim.cpp`) eliminates variables
by resolving clauses. If a variable in the Gauss matrix is eliminated,
the Gauss matrix becomes stale. Setting `elimxors=0` prevents XOR-based
elimination but doesn't prevent regular BVE.

**Options**:

A. **Protect Gauss variables from elimination** (~10 lines):
   In `elim.cpp`, skip variables that are in the Gauss matrix:
   ```cpp
   if (gauss && gauss->has_var(idx)) continue;
   ```
   This is the simplest approach. It prevents BVE from eliminating
   XOR-related variables, which may reduce BVE's effectiveness on
   some formulas but preserves Gauss matrix correctness.

B. **Update Gauss matrix on elimination** (~100 lines):
   When BVE eliminates a variable, substitute it in the Gauss matrix
   (set it to the value implied by the elimination). This is more
   complex but preserves BVE's full power.

C. **Rebuild Gauss matrix after preprocessing** (~30 lines):
   Let BVE run freely, then rebuild the Gauss matrix from the
   remaining XOR constraints. This requires re-detecting XOR patterns
   in the post-BVE clause database, which CaDiCaL's congruence module
   already does.

**Recommendation**: Start with Option A (simplest, ~10 lines). If BVE
effectiveness is a concern, move to Option C.

### Phase 5: Public API

**Files to modify**: `cadical.hpp`, `solver.cpp`

1. Add `Solver::add_xor(vector<int>, bool)` to the public API.
2. In `add_xor`, create the `GaussPropagator` and add constraints.
3. No `elimxors=0` or `congruencexor=0` needed — the Gauss matrix
   coexists with CaDiCaL's own XOR handling.

**Effort**: ~20 lines.

### Phase 6: CBMC integration

**Files to modify**: `satcheck_cadical.cpp`

1. Replace the ExternalPropagator approach with `solver->add_xor()`.
2. Remove `cadical_xor_propagator.h` (no longer needed).
3. Remove `xor_gauss.h/cpp` from CBMC (moved to CaDiCaL).

**Effort**: ~20 lines (simplification).

## Investigation Needed

Before implementing, these questions need answers:

1. **Does protecting Gauss variables from BVE hurt performance?**
   Test: run the benchmark suite with BVE disabled for XOR variables
   only. Compare with full BVE. If the difference is <10%, Option A
   is fine.

2. **Does the `gauss_reason` sentinel interact correctly with
   CaDiCaL's chronological backtracking?**
   CaDiCaL uses chronological backtracking (`opts.chrono`) which
   can skip levels. The Gauss matrix backtrack must handle this.
   Test: run with `--chrono` enabled and disabled.

3. **Does the Gauss propagation inside `propagate()` affect the
   watched-literal invariant?**
   The BCP loop maintains invariants about watched literals. Adding
   assignments inside the loop (via `search_assign`) may violate
   these. The safer approach: add Gauss propagations AFTER the BCP
   loop, then re-enter BCP.

4. **How does the Gauss matrix interact with CaDiCaL's inprocessing?**
   CaDiCaL periodically runs inprocessing (subsumption, vivification,
   etc.) which can delete or modify clauses. The Gauss matrix is
   independent of clauses, so this should be fine. But inprocessing
   can also eliminate variables (via BVE), which needs Phase 4.

## Estimated Effort

| Phase | Lines | Risk | Dependency |
|-------|------:|------|------------|
| 1. Gauss reason sentinel | 30 | Low | None |
| 2. Propagator integration | 50 | Medium | Phase 1 |
| 3. Lazy reason materialization | 40 | Medium | Phase 1 |
| 4. BVE compatibility | 10-100 | High | Phase 2 |
| 5. Public API | 20 | Low | Phase 2 |
| 6. CBMC integration | 20 | Low | Phase 5 |
| **Total** | **170-270** | | |

## Comparison with Alternatives

| Approach | Overhead | Correctness | Effort |
|----------|----------|-------------|--------|
| ExternalPropagator (current) | 2.4s fixed | ✓ all 9 benchmarks | Done |
| Native with elimxors=0 | ~0 | ✗ distrib wrong | 150 lines |
| Native with gauss_reason | ~0 | ✓ (expected) | 170-270 lines |
| CryptoMiniSat-style | ~0 | ✓ (proven) | 500+ lines |

The `gauss_reason` approach is a middle ground: it reuses CaDiCaL's
existing lazy-reason infrastructure (proven correct for
`external_reason`) but avoids the ExternalPropagator callback overhead.

## Patch Delivery

All CaDiCaL changes would be delivered as an extension to the existing
`scripts/cadical-3.0.0-patch` file. CBMC's build system already
applies this patch when downloading CaDiCaL. No upstream CaDiCaL
changes needed.

## Investigation Results

### 1. BVE impact of protecting Gauss variables

Tested on DIMACS files with CaDiCaL `--elim=0` vs default:

| Benchmark | Vars eliminated | With BVE | Without BVE | Impact |
|-----------|---------------:|--------:|-----------:|--------|
| equiv_unsat_200 | 42,756 (51%) | 17.1s | 22.6s | BVE helps 24% |
| distrib_unsat_200 | 0 (0%) | 2.9s | 2.9s | No BVE effect |
| checksum_200 | 30,202 (47%) | 60.0s | 30.2s | BVE hurts 2x |
| hash_combine_50 | 16,073 (46%) | 59.4s | 59.5s | Neutral |
| crc_100 | 37,163 (43%) | 3.8s | 9.2s | BVE helps 2.4x |

**Conclusion**: BVE eliminates ~45-51% of variables. Disabling BVE
entirely hurts crc (2.4x) and equiv (24%) but helps checksum (2x).
Protecting only Gauss variables (~15K out of ~50K) would have a
smaller impact. **Option A (protect Gauss vars) is viable** — the
Gauss speedup (10-100x) far exceeds any BVE regression.

### 2. Chronological backtracking compatibility

**Finding**: CaDiCaL's chronological backtracking (default, `chrono=1`)
does NOT simply truncate the trail. Variables at higher levels may be
**reassigned** (kept on the trail). The trail is compacted, not truncated.

**Impact**: Trail-size-based Gauss backtracking is WRONG with chrono.
The Gauss matrix would undo assignments for variables that are still
assigned in CaDiCaL.

**Required change to Phase 2**: Instead of `gauss->backtrack(trail_size)`,
hook into CaDiCaL's backtrack loop and call `gauss->unassign(var)` for
each variable that is actually unassigned (not reassigned). This requires:

1. An `unassign(var)` method on the Gauss matrix that undoes a single
   variable's assignment and restores the affected rows.
2. Integration into CaDiCaL's backtrack loop (lines 120-148 of
   `backtrack.cpp`) where variables are classified as unassigned vs
   reassigned.

This is more complex than the snapshot-based approach (~20 additional
lines) but is necessary for correctness.

**Alternative**: Disable chronological backtracking when Gauss is active
(`solver->set("chrono", 0)`). This is simpler but may hurt performance
on some formulas. Testing needed.

### 3. Gauss propagation placement in BCP

**Finding**: CaDiCaL's `propagate()` already calls `search_assign()`
internally for BCP propagations. Adding `search_assign(lit, gauss_reason)`
is safe — it extends the trail, and the BCP loop processes the new
literal on the next iteration.

**Recommended approach**:
- **Gauss notification**: INSIDE the BCP loop, after processing each
  literal's watched clauses. Only for variables in the Gauss matrix
  (`has_var` check, O(1)).
- **Gauss propagation**: AFTER the BCP loop, with an outer loop:
  ```
  do {
    run BCP to fixpoint
    check Gauss for propagations
    if Gauss propagates, search_assign and continue outer loop
  } while (Gauss propagated something)
  ```
  This avoids recursive `propagate()` calls.

### Updated effort estimate

| Phase | Lines | Risk | Notes |
|-------|------:|------|-------|
| 1. Gauss reason sentinel | 30 | Low | Mirror external_reason |
| 2. Propagator integration | 60 | Medium | +10 for chrono compat |
| 3. Lazy reason materialization | 40 | Medium | Use original XOR vars |
| 4. BVE compatibility (Option A) | 10 | Low | Protect Gauss vars |
| 5. Public API | 20 | Low | add_xor() |
| 6. CBMC integration | 20 | Low | Simplification |
| **Total** | **180** | | |
