# Reproducing the Algebraic-Solving Paper Results

This document describes how to reproduce the empirical results in
"Algebraic Solving for Bit-Vector Arithmetic in SAT-Based Decision
Procedures." All raw data referenced below is under
`doc/paper-algebraic/data/`.

## Prerequisites

- Linux (tested on Ubuntu 24.04)
- CMake 3.8+, GCC 13+, Bison, Flex, Python 3.10+, `bc`
- Disk: ~5 GB for build
- RAM: experiments use `ulimit -v 6000000` (6 GB) unless noted; the
  SABER deferred-bit-blasting study uses a 55 GB cap (see below)
- External SMT solvers for comparison: `z3`, `cvc5` (tested 1.3.3),
  and Bitwuzla 0.9.0-dev (oracle cross-checks and comparison columns)

## Building CBMC with the algebraic solver

```bash
git clone https://github.com/diffblue/cbmc.git
cd cbmc
git checkout features/adder
git submodule update --init
cmake -S . -Bbuild -DCMAKE_BUILD_TYPE=Release
cmake --build build --target cbmc --target smt2_solver -- -j$(nproc)
```

The algebraic solver is enabled by default. Per-feature ablation is
controlled by environment variables (used by the leave-one-out
ablation, §Layer ablation / Table tab:tweak-ablation):

| Variable | Effect |
|---|---|
| `DISABLE_SIMPLIFY=1` | Disable word-level simplification (layer 1) |
| `DISABLE_ALGEBRAIC=1` | Disable the whole algebraic layer (Gröbner + vanishing) |
| `DISABLE_VANISHING=1` | Disable the vanishing-polynomial test only |
| `DISABLE_ALGEBRAIC_TREE_WALK=1` | Disable the boolean tree walk in `set_to` |
| `DISABLE_TSEITIN_PROPAGATION=1` | Disable Tseitin-aware preprocessing |
| `DISABLE_INTERREDUCE=1` | Disable F4-style basis interreduction |
| `DISABLE_NONZERO_FAST_PATH=1` | Disable the `bvult 0 x` fast path |
| `DISABLE_IF_CASE_ELIM=1` | Disable parse-time push-through-ite |
| `DISABLE_DEFER_BITBLAST=1` | Disable deferred bit-blasting |
| `GROEBNER_REVERSE_ORDER=1` | Reverse Gröbner pair/equation order (ordering ablation) |

## Resource limits

Unless a table states otherwise:
```bash
ulimit -v 6000000      # 6 GB virtual memory cap
timeout -s 9 <T> ...   # per-benchmark wall-clock; SIGKILL on timeout
```
The random-polynomial suite uses `T = 10`; the SMT-COMP, SABER, custom,
and DSP suites use `T = 60` (SABER scaling uses `T = 600`).

## Soundness validation (corpus differential sweep)

Beyond the mechanised Lean proofs, soundness is validated by a
corpus-scale differential sweep: for each benchmark we compare our
verdict against z3, cvc5, and a baseline build with the algebraic
layer disabled (`DISABLE_ALGEBRAIC=1`), and against the declared
`:status`. The sweep covers all 4361 multiplication-containing
`sat`-declared SMT-COMP QF_BV benchmarks (including > 2 MB inputs)
plus a 4000-benchmark cross-corpus sample. Result: zero verdicts
attributable to the algebraic layer disagree with the oracles. A
flagged verdict is re-run with `DISABLE_ALGEBRAIC=1` to attribute it
to the algebraic layer or to the rest of the pipeline.

## Reproducing tables and figures

### Random Polynomial Identity Suite (full suite, 3498 benchmarks)

Tables `tab:random-poly-solved` and `tab:random-poly-by-category`.
Raw data: `data/randpoly-full-results.tsv` (one row per benchmark;
columns: category, declared status, then verdict for shift_add /
comba_cs / p2_algebraic / Bitwuzla / cvc5).

Benchmarks: the entire Brain subpolynomial suite (seed-23 + seed-42,
3498 files), generated from the tarballs in
`subpolynomial-encoding/benchmarks/`. The five configurations are:

```bash
# shift_add  : DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 smt2_solver --cadical F --multiplier-encoding shift-add
# comba_cs   : DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 smt2_solver --cadical F --multiplier-encoding comba-cs
# p2_algebraic (this paper) : smt2_solver --cadical F --multiplier-encoding comba-cs
# bitwuzla   : bitwuzla F
# cvc5       : cvc5 F
```
All under `ulimit -v 8000000` and a 10 s timeout. Solved = a `sat`/`unsat`
verdict; the `data/randpoly-full-results.tsv` file is aggregated by
category for the per-category table, and checked for any verdict
contradicting `:status` (none) and any cross-config disagreement (none).

### Per-tweak (leave-one-out) ablation

Table `tab:tweak-ablation`. Raw data: `data/tweak-ablation.tsv`
(columns: suite, benchmark, config, result, time). The 26-benchmark
cross-suite subset spans custom/DSP, the SMT-COMP algebra unlocks,
SABER, and the random-polynomial suite. Each row runs
`smt2_solver --cadical F --multiplier-encoding comba-cs` with one of
the `DISABLE_*` variables above set (60 s, `ulimit -v 8000000`); the
`full` config sets none and `no_algebraic` sets `DISABLE_ALGEBRAIC=1`.

### Equation-ordering ablation (Table tab:ordering)

Default vs `GROEBNER_REVERSE_ORDER=1` (and `--reorder-vars`), 5 runs each.

### Layer ablation (Table tab:ablation)

Cumulative layers (shift-only → +simplify → +algebraic → +Comba/CS) on
the 12 representative benchmarks; raw data `data/layer-ablation.tsv`.

### DSP datapath equivalence (5 benchmarks)

In the custom suite (`dsp_*`); decided by the vanishing-polynomial test.
Verdicts in `data/custom-refresh.tsv`.

### SABER polynomial multiplication (Tables tab:saber-scaling, tab:saber-defer)

Queries generated by `bench-multiplication/saber/make-saber-query.py`
(SABER reference code from the KU Leuven NIST PQC submission).
`tab:saber-defer` is measured under per-output-coefficient RSS sampling
and a 55 GB cgroup; `tab:saber-scaling` is the uninstrumented timing
(hence the small N=256 difference, 11.25 s vs 13.4 s). Refreshed
verdicts: `data/saber-refresh.tsv`.

### Custom suite (39 benchmarks, Table in §Custom Suite)

Benchmarks: `bench-multiplication/smt-comp/<name>.smt2` (names listed in
`data/paper2-suite-results.tsv`). Refreshed verdicts/timings:
`data/custom-refresh.tsv` (algebraic 39/39, comba_cs 35/39, 0 oracle
disagreements).

### SMT-COMP 2024 QF_BV community sample (66 benchmarks, Table tab:smtcomp-sample)

Benchmarks: `bench-multiplication/smt-comp-sample/*.smt2`. Refreshed
data: `data/smtcomp-sample-refresh.tsv` (algebraic verdict+time,
comba_cs verdict, z3 oracle, disagreement flag). Headline: shift-add
37/66 (PAR-2 57.1), algebraic 43/66 (PAR-2 44.8), 0 disagreements, 8
algebra unlocks. cvc5/Bitwuzla columns from `data/cvc5-smt-comp-results.tsv`
and a Bitwuzla run.

### High-bitwidth scaling (§Threats to Validity)

Raw data: `data/high-bitwidth-scaling.tsv`. To re-run:
`bench-multiplication/run-high-bitwidth-scaling.sh`.

### Amulet comparison (§Amulet2)

Discussed at the level of use-case scope (gate-level AIG vs SMT-LIB);
no direct head-to-head. Amulet source: https://github.com/d-kfmnn/amulet2.

## Mechanised Lean 4 proofs

```bash
cd formal-proofs && lake build
```
20 modules, > 150 theorems, zero `sorry`, zero project-internal axioms.
Contract-level traceability is checked by
`scripts/check_proof_traceability.py` (run from the repo root). Four
general-purpose results are prepared for Mathlib (e.g. the unit
characterisation of `ZMod (2^d)`).

## Notes on the artifact

- `doc/paper-algebraic/data/` holds the raw TSVs for every table.
- `doc/paper-algebraic/soundness-sweep-findings-2026-06-03.md` documents
  the corpus differential sweep and the bugs it found/fixed.
