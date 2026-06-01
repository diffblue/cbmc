# Corpus widening results — SMT-LIB 2024 QF\_BV

Date: 2026-06-01. Triggered by Armin's review (widen the
benchmark corpus before revisiting the remaining-work list).

## What we acquired

- **Full SMT-LIB 2024 QF\_BV** (Zenodo `10.5281/zenodo.11061097`,
  md5 `3104e6a73841bccab5a2b0960afa8576`). 35 GB uncompressed,
  **46,191 benchmarks** across 55 contributor families. Staged
  at `/home/ubuntu/bench-staging/non-incremental/QF_BV/` (not
  committed — 35 GB).
- **Konrad/Scholl gate-level archives** (FMCAD22 dividers,
  FMCAD24 multipliers, FMSD25 extended). Staged at
  `/home/ubuntu/bench-staging/konrad/`. FMCAD24 is 1,860 AIG
  files. **Blocked**: no AIG→SMT-LIB converter on this machine
  (`abc`, `aigtoaig`, `yosys` all absent). These are Item-7
  gate-level material anyway; deferred.

## Triage

Of the 46,191 QF\_BV benchmarks:
- 21,007 contain `bvmul` (our core fragment).
- **15,435** contain `bvmul` and are declared `:status unsat`
  (our verdict of interest).

By family the bvmul-unsat set is dominated by symbolic-execution
path conditions: `sage` (9929), `Sage2` (4211). The rest:
Noetzli bv-term-rw (488), Sydr (364), uclid (152), **float
(75)**, log-slicing (59), brummayerbiere2 (55), and a long tail.

## Headline result: the `float` family

`float` = bit-vector encodings of floating-point arithmetic
from Haller, Griggio, Brain, Kroening, *"Deciding floating-point
logic with systematic abstraction"*, FMCAD 2012. They contain
wide multipliers (e.g.\ 53×53→106-bit significand products),
which is exactly where our $\mathbb{Z}_{2^d}$ algebraic method
beats bit-blasting.

**Our solver dominates this family.** On all 75 float bvmul-unsat
benchmarks at 60 s (6-way parallel, low contention):

| Solver    | Solved (of 75) |
|-----------|----------------|
| **ours**  | **68**         |
| Bitwuzla  | 51             |
| cvc5      | 6              |

**18 confirmed unique wins** (standalone, 1-way, 60 s): our
solver decides 18 float benchmarks that *neither* Bitwuzla *nor*
cvc5 can solve within 60 s. All declared `unsat`; our verdict
agrees with Bitwuzla on every benchmark both solve (sound). The
18:

```
pow5.smt2                         1.3s
test_v5_r10_vr10_c1_s15708.smt2  15.6s
test_v5_r10_vr10_c1_s21502.smt2  13.5s
test_v5_r10_vr10_c1_s7608.smt2   13.6s
test_v5_r10_vr5_c1_s8690.smt2    17.7s
test_v5_r15_vr10_c1_s14516.smt2  25.7s
test_v5_r15_vr10_c1_s25268.smt2  26.4s
test_v5_r15_vr1_c1_s26845.smt2   25.2s
test_v5_r15_vr1_c1_s32559.smt2   24.7s
test_v5_r15_vr1_c1_s8236.smt2    26.6s
test_v5_r15_vr5_c1_s23844.smt2   25.3s
test_v5_r15_vr5_c1_s26657.smt2   27.5s
test_v5_r15_vr5_c1_s8246.smt2    25.4s
test_v7_r12_vr10_c1_s18160.smt2  31.9s
test_v7_r12_vr1_c1_s10576.smt2   31.9s
test_v7_r12_vr1_c1_s22787.smt2   31.9s
test_v7_r12_vr1_c1_s703.smt2     31.8s
test_v7_r7_vr1_c1_s24449.smt2    17.8s
```

Plus several where we beat cvc5 (TO) and are 3–7× faster than
Bitwuzla (the `newton.*` benchmarks).

This is significant: our paper currently claims 4 wins-beyond-
all-current-solvers (Brain's random-polynomial sample). The
float family adds **18 more**, in a benchmark set published by a
co-author (Brain) and entirely absent from our 66-benchmark
SMT-COMP sample.

## Methodological note: parallel contention

A first pass at 36-way parallelism (= core count) inflated solve
times enough to manufacture spurious timeouts: `newton.3.3.i`
"won" at 36-way but Bitwuzla solves it standalone in 31 s. All
win claims here are re-confirmed at low parallelism (1- to
6-way). **Lesson for the paper's evaluation: report numbers at
≤ (cores/4)-way parallelism, or single-threaded.**

## Broad-corpus picture (stratified 555-benchmark sample)

Across a 60-per-family stratified sample of the bvmul-unsat set
(60 s, with the contention caveat above): ours 329, cvc5 373,
Bitwuzla 444. We trail the mature general solvers overall — as
expected for a specialised pre-solver — but win decisively on
the arithmetic-identity-shaped subset (float) and lose on
symbolic-execution path conditions (Sydr, Sage2) and gate-level
families (brummayerbiere2). The unique-failure distribution:

```
Sydr 59, Sage2 24, brummayerbiere2 13, Noetzli 5, log-slicing 2
```

These map onto Item 10's gates: Sydr/Sage2 are Gate B (non-
polynomial operators) + Gate D (budget); brummayerbiere2 is
gate-level (Item 7).

## Files in this directory

- `pow5.smt2`, `mul_03_30_4.smt2` — two smallest clean wins,
  committed as concrete artifacts (both `unsat`, both solved by
  us in < 2 s, both TO on Bitwuzla and cvc5).
- `MANIFEST.tsv` — SHA256 + size + relpath for all 75 float
  bvmul-unsat benchmarks, for reproducible re-fetch from the
  Zenodo release.
- `results-{ours,bitwuzla,cvc5}.tsv` — full per-benchmark
  verdict + wall-time (6-way parallel, 60 s).
- `run-any.sh` — the evaluation harness (stdin/filearg modes).

## Reproduce

```bash
# 1. fetch + extract QF_BV (1.7 GB compressed, 35 GB extracted)
curl -L -o QF_BV.tar.zst \
  https://zenodo.org/records/11061097/files/QF_BV.tar.zst?download=1
tar --zstd -xf QF_BV.tar.zst
# 2. run the harness on the float family (paths from MANIFEST.tsv)
./run-any.sh <list> 60 6 out.tsv tag stdin <smt2_solver>
```
