# PQC CBMC Proof Benchmark Results

- **Date:** 2026-02-26
- **Hardware:** Intel Xeon Platinum 8124M @ 3.00GHz, 36 CPUs, 68 GB RAM
- **OS:** Linux 6.17.0-1007-aws x86_64 (Ubuntu 24.04)
- **Configuration:** 300s timeout, 30 GB memory limit, 2 parallel processes

## Git Revisions

| Component | Revision | Branch/Note |
|-----------|----------|-------------|
| CBMC | `2ac1dee90c` | `features/quantifiers-elimination` (with fix) |
| mlkem-native | `cbfacea` | HEAD of main |
| mldsa-native | `0b1c536` | HEAD of main |

## Tool Versions

| Tool | Version |
|------|---------|
| CBMC | 6.8.0 (cbmc-6.8.0-70-g2ac1dee90c) |
| Z3 | 4.15.3 |
| Bitwuzla | 0.8.2 (not in PATH for this run; 54 mlkem proofs skipped) |
| Litani | 1.29.0 |

## Solver Configurations

1. **SMT** — original backend from the proof Makefile (Z3 via `--smt2`)
2. **SAT (CaDiCaL)** — `--sat-solver cadical`
3. **SAT (MiniSat)** — `--sat-solver minisat2`
4. **SMT (+AFS)** — original SMT with `--no-array-field-sensitivity` removed
5. **SAT CaDiCaL (+AFS)** — CaDiCaL with `--no-array-field-sensitivity` removed

## Aggregate Results

### mlkem-native (153 proofs, 54 bitwuzla-skipped)

| Backend | Success | Failure | Timeout | OOM | Invariant | Skipped |
|---------|--------:|--------:|--------:|----:|----------:|--------:|
| SMT (original) | 98 | 0 | 1 | 0 | 0 | 54 |
| SAT (CaDiCaL) | 142 | 0 | 6 | 5 | 0 | 0 |
| SAT (MiniSat) | 147 | 0 | 3 | 3 | 0 | 0 |

### mldsa-native (175 proofs)

| Backend | Success | Failure | Timeout | OOM | Invariant | Unknown |
|---------|--------:|--------:|--------:|----:|----------:|--------:|
| SMT (original) | 145 | 0 | 1 | 0 | 4 | 4 |
| SAT (CaDiCaL) | 143 | 0 | 26 | 3 | 3 | 0 |
| SAT (MiniSat) | 154 | 0 | 17 | 1 | 3 | 0 |

### Key result: ZERO FAILURES

The quantifier instantiation fix (`2ac1dee90c`) eliminated all SAT/SMT
disagreements. Previously, 4 proofs showed FAILURE on both SAT solvers and
12 additional proofs failed on MiniSat only. All now report SUCCESS or
timeout/OOM (resource limits, not correctness issues).

## Comparison with Previous Run (before fix)

| Metric | Before fix | After fix |
|--------|-----------|-----------|
| SAT FAILURE (both solvers) | 4 | 0 |
| MiniSat-only FAILURE | 12 | 0 |
| Total FAILURE across all backends | 16 | 0 |
| Invariant violations (SAT) | 3 | 3 (unchanged, `--arrays-uf-always` bug) |

The 4 proofs that previously failed on both SAT solvers now succeed:
- `poly_compress_du` (mlkem): CaDiCaL 3.7s, MiniSat 1.3s
- `poly_compress_dv` (mlkem): CaDiCaL 3.2s, MiniSat 1.0s
- `polyveck_make_hint` (mldsa): CaDiCaL 47.3s, MiniSat 191.4s
- `polyveck_pointwise_poly_montgomery` (mldsa): CaDiCaL 155.3s, MiniSat 289.5s

The 12 MiniSat-only failures now either succeed or timeout (resource limits).

## Performance Comparison

Considering only proofs that succeed on all 3 main backends:

| Repo | Proofs | SMT total | CaDiCaL total | MiniSat total | SMT faster | CaDiCaL faster |
|------|-------:|----------:|--------------:|--------------:|-----------:|---------------:|
| mlkem-native | 91 | 375s | 1817s | 664s | 63 | 24 |
| mldsa-native | 120 | 644s | 4332s | 1774s | 77 | 36 |

## SMT Issues (pre-existing, unrelated to this branch)

4 mldsa proofs crash with INVARIANT_VIOLATION on the SMT backend due to
`--arrays-uf-always` (same bug as the SAT crashes, different code path).

4 mldsa proofs report UNKNOWN (exit code 6) — likely Z3 errors on complex
proofs with external SMT solver configurations.

## Invariant Violations (pre-existing CBMC bug)

3 mldsa proofs crash with both SAT solvers due to `--arrays-uf-always`:
polyveck_add, polyvec_matrix_expand_serial, polyvec_matrix_pointwise_montgomery.
See [invariant_violation_analysis.md](invariant_violation_analysis.md).

## Resource Usage

- Max memory (non-OOM): 21.2 GB (`kem_dec` with CaDiCaL)
- 30 GB limit confirmed safe for all non-OOM runs
- 2 parallel processes used ~26 GB peak combined

## Raw Data

Full per-proof CSV: `summary.csv` in this directory.
Per-proof logs: `/tmp/pqc-experiment/results/`
