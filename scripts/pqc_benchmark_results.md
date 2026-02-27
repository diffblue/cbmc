# PQC CBMC Proof Benchmark Results

- **Date:** 2026-02-27
- **Hardware:** Intel Xeon Platinum 8124M @ 3.00GHz, 36 CPUs, 68 GB RAM
- **OS:** Linux 6.17.0-1007-aws x86_64 (Ubuntu 24.04)
- **Configuration:** 300s timeout, 30 GB memory limit, 2 parallel processes

## Git Revisions

| Component | Revision | Branch/Note |
|-----------|----------|-------------|
| CBMC | `83d65e62aa` | `features/quantifiers-elimination` (all fixes applied) |
| mlkem-native | `cbfacea` | HEAD of main |
| mldsa-native | `0b1c536` | HEAD of main |

## Tool Versions

| Tool | Version |
|------|---------|
| CBMC | 6.8.0 (cbmc-6.8.0-78-g83d65e62aa) |
| Z3 | 4.15.3 |
| Bitwuzla | 0.8.2 |
| Litani | 1.29.0 |

## Solver Configurations

1. **SMT** — original backend from the proof Makefile (Z3 via `--smt2` or Bitwuzla via `--bitwuzla`)
2. **SAT (CaDiCaL)** — `--sat-solver cadical`
3. **SAT (MiniSat)** — `--sat-solver minisat2`

## Aggregate Results

### mlkem-native (153 proofs)

| Backend | Success | Failure | Timeout | OOM |
|---------|--------:|--------:|--------:|----:|
| SMT (original) | 153 | 0 | 0 | 0 |
| SAT (CaDiCaL) | 142 | 0 | 6 | 5 |
| SAT (MiniSat) | 147 | 0 | 3 | 3 |

### mldsa-native (175 proofs)

| Backend | Success | Failure | Timeout | OOM |
|---------|--------:|--------:|--------:|----:|
| SMT (original) | 174 | 0 | 1 | 0 |
| SAT (CaDiCaL) | 144 | 0 | 27 | 4 |
| SAT (MiniSat) | 154 | 0 | 20 | 1 |

### Zero soundness issues

All three fixes applied:
1. Quantifier instantiation for array literals in SSA (`2ac1dee90c`)
2. Accept member expressions with arbitrary struct operands (`96c388bd7e`)
3. Bypass array theory for member-of-index expressions (`fc767662c9`)
4. Connect array symbol map literals to element-wise constraints (`83d65e62aa`)

Result: **0 FAILURE across all 328 proofs × 3 backends**. All non-SUCCESS
results are TIMEOUT or OOM — no spurious counterexamples, no crashes.

### Previously-failing proofs

| Proof | SMT | CaDiCaL (before) | CaDiCaL (now) | MiniSat (before) | MiniSat (now) |
|-------|-----|-------------------|---------------|-------------------|---------------|
| polyveck_add | SUCCESS | FAILURE | TIMEOUT | FAILURE | TIMEOUT |
| polyvec_matrix_pointwise_montgomery | SUCCESS | FAILURE | TIMEOUT | FAILURE | TIMEOUT |

The `--arrays-uf-always` soundness fix eliminated the spurious counterexamples.
These proofs now timeout on SAT (the additional constraints from the fix make
the SAT encoding harder), but produce no incorrect results.

## Memory Statistics (successful proofs only)

| Backend | Max | Avg | Median | Count |
|---------|----:|----:|-------:|------:|
| SMT | 3669 MB | 119 MB | 48 MB | 327 |
| CaDiCaL | 21658 MB | 773 MB | 203 MB | 286 |
| MiniSat | 13508 MB | 524 MB | 105 MB | 301 |

SMT uses ~6.5x less memory on average than CaDiCaL and ~4.4x less than MiniSat.

## Resource Usage

- Max memory (non-OOM): 21658 MB = 21.2 GB (`kem_dec` with CaDiCaL)
- 30 GB limit confirmed safe for all non-OOM runs
- 2 parallel processes: ~26 GB peak combined, well within 68 GB RAM
- Total wall time: ~6 hours

## Raw Data

Full per-proof CSV: `summary.csv` in this directory.
Analysis documents: `invariant_violation_analysis.md`, `sat_failure_analysis.md`
Reproducers: `reproducers/`
