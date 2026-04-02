# Native CaDiCaL Gaussian Elimination Patch

This directory contains a patch for CaDiCaL 3.0.0 that adds native
Gaussian elimination support, bypassing the ExternalPropagator API
to eliminate callback overhead.

## Status: EXPERIMENTAL — has correctness bugs

The native integration produces wrong UNSAT results on some formulas.
The bug manifests at Gauss matrix rank >= 10 and is in the reason/conflict
clause generation or the row reduction/backtracking logic.

The ExternalPropagator approach (`src/solvers/sat/cadical_xor_propagator.h`)
has the same underlying bug — it was just not caught until we ran the full
CBMC regression suite with `--sat-solver cadical --xor-gauss`.

## Performance (when it was working)

The native integration eliminated all callback overhead:
- distrib_unsat_200: 8.1s → 0.016s (was a regression with ExternalPropagator)
- hash_combine_50: 37s → 0.003s (10,800x)
- popcount_10: 30s → 0.02s (1,500x)

## Files

- `gauss_propagator.hpp` — The GF(2) Gaussian elimination engine
  (header-only, placed in `build/cadical-src/src/`)
- `cadical-native.patch` — Unified diff against CaDiCaL 3.0.0
  (apply to `build/cadical-src/`)

## Integration points in CaDiCaL

1. `solver.cpp` — `Solver::add_xor()` method
2. `internal.hpp` — `GaussPropagator *gauss` member, `gauss_reason` clause
3. `propagate.cpp` — Gauss assign during BCP, Gauss propagation after BCP fixpoint
4. `backtrack.cpp` — Gauss unassign during backtracking
5. `analyze.cpp` — `gauss_reason` handling (like `external_reason`)
6. `collect.cpp` — Skip `gauss_reason` during garbage collection
7. `elim.cpp` / `elimfast.cpp` — Skip BVE on Gauss variables

## Known bugs

1. Wrong UNSAT results when rank >= 10 (reason clauses may be invalid)
2. The i2e variable mapping during BCP may be incorrect for
   eliminated/substituted variables
3. Conflict clauses use `original_xors` which may reference variables
   not present in the reduced matrix row
