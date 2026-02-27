# PQC CBMC Proof Benchmark Results

- **Date:** 2026-02-27
- **Hardware:** Intel Xeon Platinum 8124M @ 3.00GHz, 36 CPUs, 68 GB RAM
- **OS:** Linux 6.17.0-1007-aws x86_64 (Ubuntu 24.04)
- **Configuration:** 300s timeout, 30 GB memory limit, 2 parallel processes

## Git Revisions

| Component | Revision | Branch/Note |
|-----------|----------|-------------|
| CBMC | `e1e84df8c1` | `features/quantifiers-elimination` (with quantifier + arrays fixes) |
| mlkem-native | `cbfacea` | HEAD of main |
| mldsa-native | `0b1c536` | HEAD of main |

## Tool Versions

| Tool | Version |
|------|---------|
| CBMC | 6.8.0 (cbmc-6.8.0-74-ge1e84df8c1) |
| Z3 | 4.15.3 |
| Bitwuzla | 0.8.2 |
| Litani | 1.29.0 |

## Solver Configurations

1. **SMT** — original backend from the proof Makefile (Z3 via `--smt2` or Bitwuzla via `--bitwuzla`)
2. **SAT (CaDiCaL)** — `--sat-solver cadical`
3. **SAT (MiniSat)** — `--sat-solver minisat2`
4. **SMT (+AFS)** — original SMT with `--no-array-field-sensitivity` removed
5. **SAT CaDiCaL (+AFS)** — CaDiCaL with `--no-array-field-sensitivity` removed

## Aggregate Results

### mlkem-native (153 proofs)

| Backend | Success | Failure | Timeout | OOM | Invariant |
|---------|--------:|--------:|--------:|----:|----------:|
| SMT (original) | 153 | 0 | 0 | 0 | 0 |
| SAT (CaDiCaL) | 142 | 0 | 6 | 5 | 0 |
| SAT (MiniSat) | 147 | 0 | 3 | 3 | 0 |
| SMT (+AFS) | 11/11 | 0 | 0 | 0 | 0 |
| SAT CaDiCaL (+AFS) | 8/11 | 0 | 0 | 3 | 0 |

### mldsa-native (175 proofs)

| Backend | Success | Failure | Timeout | OOM |
|---------|--------:|--------:|--------:|----:|
| SMT (original) | 174 | 0 | 1 | 0 |
| SAT (CaDiCaL) | 144 | 2 | 25 | 4 |
| SAT (MiniSat) | 154 | 2 | 18 | 1 |
| SMT (+AFS) | 24/24 | 0 | 0 | 0 |
| SAT CaDiCaL (+AFS) | 16/24 | 0 | 7 | 1 |

### Key improvements over previous runs

| Issue | Before arrays fix | After arrays fix |
|-------|-------------------|------------------|
| Invariant violations (crashes) | 3-7 | 0 |
| SAT FAILURE (quantifier bug) | 16 | 0 (fixed in `2ac1dee90c`) |
| SAT FAILURE (`--arrays-uf-always`) | N/A (was crashing) | 2 proofs × 2 solvers |
| Bitwuzla proofs skipped | 54 | 0 |
| mlkem SMT success | 98 | 153 |

### Remaining 4 SAT failures

Two mldsa proofs fail on both SAT solvers while SMT succeeds. Both use
`--arrays-uf-always`, which is now handled without crashing but produces
incorrect results on these specific proofs:

| Proof | SMT | CaDiCaL | MiniSat |
|-------|-----|---------|---------|
| polyveck_add | SUCCESS (5.2s) | FAILURE (124s) | FAILURE (119s) |
| polyvec_matrix_pointwise_montgomery | SUCCESS (0.3s) | FAILURE (120s) | FAILURE (120s) |

These are SAT-specific soundness issues with `--arrays-uf-always` mode,
distinct from the quantifier instantiation bug (which is fixed).

## Performance Comparison

Proofs succeeding on all 3 main backends:

### mlkem-native (140 proofs)

| Backend | Time (total) | Mem (max) | Mem (avg) | Mem (median) |
|---------|-------------:|----------:|----------:|-------------:|
| SMT | 628s | 339 MB | 65 MB | — |
| CaDiCaL | 2149s | 21658 MB | 593 MB | — |
| MiniSat | 1009s | 6479 MB | 227 MB | — |

### mldsa-native (142 proofs)

| Backend | Time (total) | Mem (max) | Mem (avg) | Mem (median) |
|---------|-------------:|----------:|----------:|-------------:|
| SMT | 459s | 404 MB | 68 MB | — |
| CaDiCaL | 5257s | 6958 MB | 926 MB | — |
| MiniSat | 2220s | 1952 MB | 318 MB | — |

### Memory Statistics (all successful proofs)

| Backend | Max | Avg | Median | Count |
|---------|----:|----:|-------:|------:|
| SMT | 3669 MB | 119 MB | 48 MB | 327 |
| CaDiCaL | 21658 MB | 826 MB | 208 MB | 288 |
| MiniSat | 13509 MB | 539 MB | 106 MB | 303 |

SMT uses 7x less memory on average than CaDiCaL and 4.5x less than MiniSat.

### Top SAT Wins (CaDiCaL speedup over SMT)

| Proof | Repo | SMT time/mem | CaDiCaL time/mem | Speedup |
|-------|------|-------------|------------------|--------:|
| fqmul | mlkem | 7.3s / 54MB | 0.2s / 56MB | 29x |
| ct_memcmp | mldsa | 26.1s / 56MB | 0.8s / 84MB | 34x |
| poly_frombytes_native | mlkem | 9.8s / 64MB | 1.2s / 157MB | 8x |
| poly_reduce_native | mlkem | 18.0s / 97MB | 4.0s / 236MB | 4x |
| rej_uniform_c | mlkem | 107.0s / 80MB | 25.0s / 1401MB | 4x |

### Top SMT Wins (CaDiCaL slowdown vs SMT)

| Proof | Repo | SMT time/mem | CaDiCaL time/mem | Slowdown |
|-------|------|-------------|------------------|--------:|
| polyvecl_permute_bitrev_to_custom | mldsa | 0.1s / 34MB | 35.1s / 638MB | 319x |
| poly_reduce | mldsa | 0.5s / 47MB | 143.3s / 4989MB | 319x |
| poly_sub | mldsa | 0.5s / 48MB | 152.0s / 5337MB | 282x |
| polymat_permute_bitrev_to_custom | mlkem | 3.2s / 193MB | 276.3s / 3214MB | 87x |
| poly_invntt_tomont_c | mlkem | 1.0s / 74MB | 84.9s / 3278MB | 84x |

## Resource Usage

- Max memory (non-OOM): 21658 MB = 21.2 GB (`kem_dec` with CaDiCaL)
- 30 GB limit confirmed safe for all non-OOM runs
- 2 parallel processes: ~26 GB peak combined, well within 68 GB RAM
- Total wall time: ~6 hours

## Raw Data

Full per-proof CSV: `summary.csv` in this directory.
Analysis documents: `invariant_violation_analysis.md`, `sat_failure_analysis.md`
Reproducers: `reproducers/`
