# PQC Benchmark Context — For Resuming Work

## OBJECTIVE
Evaluate CBMC's SAT backend (MiniSat/CaDiCaL) against SMT (Z3/Bitwuzla) on mlkem-native (153 proofs) and mldsa-native (175 proofs) from the `features/quantifiers-elimination` branch. All bugs found have been fixed. Five benchmark runs completed; the fifth (final) run has zero FAILURE results.

## BRANCH STATE

### Commits on branch (oldest to newest)
```
69e12ecb75 Eager quantifier elimination: support empty ranges
48f4060f13 Quantifier instantiation via simplistic E-matching
3c705306fb Complete instantiation for quantifier elimination with offsets
58df3ac5ad Regression tests for complete quantifier instantiation
ad3aa10264 Set 20-minute timeout for all CMake-based regression tests
9774e37369 Add per-test timeout support (-t) to test.pl
1c243c5c28 Regression test: --arrays-uf-always crash on array-of-structs
472a81ec41 Regression test: forall with variable bound
805285e20a Analysis documents and reproducers for SAT backend issues
2ac1dee90c Fix quantifier instantiation for array literals in SSA
2dba58509e Re-run PQC benchmarks with quantifier fix, 30GB limit, 2 parallel
96c388bd7e Accept member expressions with arbitrary struct operands in array solver
19ed6214be Upgrade arrays-uf-always test from KNOWNBUG to CORE
e1e84df8c1 Fix benchmark script to find tools from previous --install-deps run
66fa04c0e2 Re-run PQC benchmarks with arrays fix, bitwuzla, memory stats
135bb7cee1 Regression test: --arrays-uf-always soundness issue on array-of-structs
fc767662c9 Fix --arrays-uf-always soundness for member-of-index expressions
83d65e62aa Connect array symbol map literals to element-wise constraints
5965647862 Re-run PQC benchmarks with arrays-uf-always soundness fix
```

### CBMC build
- Binary: `/home/ubuntu/cbmc-github.git/build/bin/cbmc`
- Version: `6.8.0 (cbmc-6.8.0-78-g83d65e62aa)`
- Includes all fixes: quantifier instantiation, arrays.cpp member expressions, boolbv_index.cpp member-of-index bypass, boolbv.cpp map-literal-to-element connection

## BUGS FOUND AND FIXED

### 1. Quantifier instantiation for array literals (commit 2ac1dee90c)
- **File:** `src/solvers/flattening/boolbv_quantifier.cpp` (~line 530)
- **Root cause:** After SSA, arrays in quantifier bodies become `array_exprt` literals. `collect_ground_indices()` can't match these against SSA symbols in the cache, returns empty set → forall instantiated with zero terms → vacuously true → spurious counterexamples.
- **Fix:** When a context's array is `array_exprt`, add indices 0..size-1 directly (capped at 256).
- **Regression test:** `regression/cbmc/Quantifiers-variable-bound/`

### 2. arrays.cpp invariant violation (commit 96c388bd7e)
- **File:** `src/solvers/flattening/arrays.cpp` (lines ~193-198, ~507-513)
- **Root cause:** Overly strict invariant required member expressions to have symbol/nondet_symbol struct operands. Crashed on `member(index(...), field)`.
- **Fix:** Accept member expressions with arbitrary struct operands.
- **Regression test:** `regression/cbmc/arrays-uf-always-member-crash/` (CORE)

### 3. --arrays-uf-always soundness for member-of-index (commit fc767662c9)
- **File:** `src/solvers/flattening/boolbv_index.cpp` (~line 34-48)
- **Root cause:** `member(index(outer_array, i), field)` treated as opaque by array theory → unconstrained bitvector.
- **Fix:** Bypass array theory for member expressions with non-symbol struct operands when array has known finite size.
- **Regression test:** `regression/cbmc/arrays-uf-always-member-soundness/` (CORE)

### 4. --arrays-uf-always soundness for large structs (commit 83d65e62aa)
- **File:** `src/solvers/flattening/boolbv.cpp` (~line 508-550)
- **Root cause:** Symbol arrays have disconnected map literals (used in struct contexts) and element-wise free variables (from array theory). For structs with array members ≥65 elements, the map literals were unconstrained.
- **Fix:** In `boolbv_set_equality_to_true`, connect map literals to element-wise bitvectors for arrays with known finite size ≤ MAX_FLATTENED_ARRAY_SIZE.
- **Regression test:** `regression/cbmc/arrays-uf-always-large-struct-soundness/` (CORE)

## FINAL BENCHMARK RESULTS (Run 5)

```
mlkem-native (153 proofs):
  smt:         SUCCESS=153
  sat_cadical: SUCCESS=142, TIMEOUT=6, OOM=5
  sat_minisat: SUCCESS=147, TIMEOUT=3, OOM=3

mldsa-native (175 proofs):
  smt:         SUCCESS=174, TIMEOUT=1
  sat_cadical: SUCCESS=144, TIMEOUT=27, OOM=4
  sat_minisat: SUCCESS=154, TIMEOUT=20, OOM=1

Memory stats (successful proofs):
  smt:         max=3669MB  avg=119MB  median=48MB   (n=327)
  sat_cadical: max=21658MB avg=773MB  median=203MB  (n=286)
  sat_minisat: max=13508MB avg=524MB  median=105MB  (n=301)

FAILURE count: 0 (was 4 before fix2.patch, 16 before quantifier fix)
```

### Timeout/OOM root causes (46 proofs)
1. **Keccak + --no-array-field-sensitivity** (5 proofs): Array theory Ackermann constraints blow up 170-484x. No quantifiers. SMT is the right backend.
2. **Quantifier-heavy DFCC proofs** (41 proofs): Quantifier instantiation expands forall over 256-element arrays into conjunctions. 4-327x blowup. Nested quantifiers (K×N terms) are worst.
3. **polyvec_matrix_expand_serial** (1 proof): Large matrix, no quantifiers, 28x blowup.
- 84% of timeouts are memory-bound (>1GB). 9 low-memory MiniSat timeouts are CPU-bound.

## KEY FILES

| File | Purpose |
|------|---------|
| `scripts/run_pqc_proofs.sh` | Benchmark script (--parallel, --memlimit, auto-PATH) |
| `scripts/pqc_benchmark_results.md` | Results summary (run 5) |
| `scripts/summary.csv` | Per-proof CSV (run 5) |
| `scripts/timeout_oom_analysis.md` | Timeout/OOM root cause analysis |
| `scripts/sat_failure_analysis.md` | SAT failure + arrays-uf-always analysis |
| `scripts/invariant_violation_analysis.md` | Invariant violation analysis |
| `scripts/reproducers/` | Standalone C reproducers for all bugs |
| `/tmp/pqc-experiment/results/` | Raw results from run 5 (meta files per proof) |
| `/tmp/pqc-experiment/run5.log` | Run 5 log |

## HARDWARE
- Intel Xeon Platinum 8124M @ 3.00GHz, 36 CPUs, 68 GB RAM, no swap
- 30 GB per-proof limit, 2 parallel processes

## COMMIT GUIDELINES
- Each commit focused on a single feature with descriptive message
- All commits need `Co-authored-by: Kiro (autonomous agent) <kiro-agent@users.noreply.github.com>`
