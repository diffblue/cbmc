# Timeout/OOM Root Cause Analysis

- **Date:** 2026-02-27
- **CBMC:** 6.8.0 (cbmc-6.8.0-78-g83d65e62aa)
- **Configuration:** 300s timeout, 30 GB memory limit, 2 parallel processes

## Overview

46 of 328 proofs (14%) have SAT timeout or OOM on at least one backend.
They fall into 3 distinct categories by root cause.

## Category 1: Keccak + `--no-array-field-sensitivity` (5 proofs)

All OOM on CaDiCaL (28–29 GB), 4 of 5 OOM on MiniSat too.
Zero quantifiers. All use `--no-array-field-sensitivity`.

| Proof | SMT | CaDiCaL | MiniSat | Blowup |
|-------|----:|--------:|--------:|-------:|
| keccak_squeeze_once (mlkem) | 60 MB | 28914 MB OOM | 26640 MB OOM | 484x |
| keccak_squeezeblocks (mlkem) | 97 MB | 28957 MB OOM | 26680 MB OOM | 298x |
| keccak_squeezeblocks_x4 (mlkem) | 159 MB | 28328 MB OOM | 26957 MB OOM | 178x |
| keccak_squeezeblocks_x4 (mldsa) | 165 MB | 28328 MB OOM | 26957 MB OOM | 172x |
| rej_uniform_native_aarch64 (mlkem) | 89 MB | 29279 MB OOM | 13505 MB OK | 327x |

**Root cause:** Without array field sensitivity, the SAT solver reasons about
the full byte-level array representation of the Keccak state. The array theory
generates massive Ackermann constraints for every pair of array accesses. SMT
solvers handle this efficiently via native array theory (select/store axioms
instantiated on demand), but the SAT encoding materializes all constraints
upfront.

**Mitigation:** These proofs require `--no-array-field-sensitivity` for
correctness with SMT. On SAT, array field sensitivity is the default and works
correctly, but the proofs were designed for SMT. No action needed — SMT is the
right backend for these proofs.

## Category 2: Quantifier-heavy DFCC proofs (41 proofs)

All have quantifiers (25–1244 per proof). Mostly mldsa-native.
Memory blowup 4–327x over SMT.

### Sub-patterns by blowup ratio (CaDiCaL memory / SMT memory)

| Blowup | Count | Example | SMT | CaDiCaL |
|--------|------:|---------|----:|--------:|
| >100x | 6 | poly_add (mlkem) | 47 MB | 7099 MB |
| 50–100x | 6 | ntt_layer (mldsa) | 223 MB | 17862 MB |
| 10–50x | 23 | polyveck_ntt (mldsa) | 273 MB | 5422 MB |
| <10x | 6 | sign_verify_internal (mldsa) | 3669 MB | 14791 MB |

**Root cause:** Quantifier instantiation expands `forall` expressions into
conjunctions. With arrays of 256 elements (MLDSA_N), each quantifier generates
up to 256 ground terms. Nested quantifiers (`forall i < K: forall j < N: ...`)
generate K×N terms. The SAT encoding of these expanded formulas is much larger
than the SMT encoding where Z3/Bitwuzla handle quantifiers natively via
E-matching and MBQI.

The blowup ratio correlates inversely with the base formula size:
- Small SMT proofs (<200 MB) see extreme blowup because quantifier expansion
  dominates the formula.
- Large SMT proofs (>1 GB) see moderate blowup because the base formula
  already accounts for most of the memory.

**Mitigation options:**
1. Lazy quantifier instantiation (only instantiate when needed by the solver)
2. Incremental instantiation (start with a subset, add more on counterexample)
3. Quantifier-aware SAT preprocessing to reduce redundant clauses
4. Accept SMT as the better backend for quantifier-heavy proofs

## Category 3: polyvec_matrix_expand_serial (1 proof)

No quantifiers, no `--no-array-field-sensitivity`. OOM on CaDiCaL (29 GB),
timeout on MiniSat (12.8 GB). SMT uses 1034 MB. 28x blowup.

**Root cause:** Large matrix expansion with complex array operations. The
formula is inherently large.

## Low-Memory Timeouts

9 proofs timeout on MiniSat with <2 GB memory. These are CPU-bound, not
memory-bound — the formula fits in memory but MiniSat can't solve it within
300s.

| Proof | MiniSat mem | SMT time | CaDiCaL |
|-------|------------:|---------:|---------|
| poly_chknorm (mldsa) | 229 MB | 0.2s | SUCCESS |
| poly_chknorm_native (mldsa) | 255 MB | 0.4s | SUCCESS |
| nttunpack_native_x86_64 (mlkem) | 827 MB | 0.6s | SUCCESS |
| polyvec_add (mlkem) | 1294 MB | 21.0s | SUCCESS |
| polyvecl_chknorm (mldsa) | 1342 MB | 1.7s | TIMEOUT |
| poly_chknorm_c (mldsa) | 1390 MB | 11.5s | TIMEOUT |
| polyveck_chknorm (mldsa) | 1486 MB | 1.5s | TIMEOUT |
| polyveck_ntt (mldsa) | 1900 MB | 6.0s | TIMEOUT |
| polyveck_invntt_tomont (mldsa) | 1905 MB | 5.8s | TIMEOUT |

CaDiCaL succeeds on 4 of these 9 proofs, suggesting the issue is MiniSat's
solver heuristics rather than a fundamental encoding problem.

## Correlation Summary

- **84% of timeouts** (48/57) use >1 GB memory → memory-bound
- **16% of timeouts** (9/57) use <2 GB memory → CPU-bound (all MiniSat)
- **100% of OOMs** (13/13) hit 26–29 GB → formula too large for 30 GB limit
- **Primary driver:** quantifier instantiation (41/46 problem proofs)
- **Secondary driver:** array theory without field sensitivity (5/46)
