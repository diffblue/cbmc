# Reproducing Paper 2 Results

This document describes how to reproduce the empirical results in the paper
"Algebraic Solving for Bit-Vector Arithmetic in Bounded Model Checking."

## Prerequisites

- Linux (tested on Ubuntu 24.04)
- CMake 3.8+, GCC 13+, Bison, Flex, Python 3.10+, `bc`
- Disk: ~5 GB for build
- RAM: 8 GB minimum (experiments use `ulimit -v 6000000`)
- External SMT solvers for comparison: `cvc5` (tested 1.3.3), and optionally Bitwuzla

## Building CBMC with the algebraic solver

```bash
git clone https://github.com/diffblue/cbmc.git
cd cbmc
git checkout features/adder
git submodule update --init
cmake -S . -Bbuild -DCMAKE_BUILD_TYPE=Release
cmake --build build --target cbmc --target smt2_solver -- -j$(nproc)
```

The algebraic solver is enabled by default. Ablation control via environment
variables:

| Variable | Effect |
|---|---|
| `DISABLE_SIMPLIFY=1` | Disable word-level simplification (layer 1) |
| `DISABLE_ALGEBRAIC=1` | Disable Gröbner-basis + vanishing-polynomial layers (2+3) |
| `DISABLE_VANISHING=1` | Disable vanishing-polynomial test only (layer 2) |
| `GROEBNER_REVERSE_ORDER=1` | Reverse equation order in Gröbner (for §2.2 ablation) |

## Resource limits

All experiments should use:
```bash
ulimit -v 6000000      # 6 GB virtual memory cap
timeout -s 9 60 ...    # 60s wall clock; SIGKILL on timeout
```

## Reproducing tables and figures

### Table (bitwidth scaling, §2.5)

Raw data: `data/scaling-results.tsv` (if present in Paper 1's artifact). To re-run:
```bash
for bench in comm assoc; do
  for bw in 8 16 32 64 128 256; do
    f=bench-multiplication/smt-comp/${bench}_${bw}.smt2
    for run in 1 2 3 4 5; do
      time build/bin/smt2_solver --cadical "$f"
    done
  done
done
```

### High-bitwidth scaling for non-trivial polynomial identities (§Limitations)

Raw data: `data/high-bitwidth-scaling.tsv`. To re-run:
```bash
bench-multiplication/run-high-bitwidth-scaling.sh
```
Tests commutativity, associativity, $(a+b)^2$, and $(a-b)(a+b)$ at
$d \in \{64, 128, 256, 512, 1024, 2048, 4096\}$ with the algebraic
procedure and (at $d \leq 256$) shift-add bit-blasting.

### Table (layer ablation, §3)

Raw data: `data/layer-ablation.tsv` (mirror of Paper 1 data; authoritative copy in `~/multiplier-encodings.git/paper-bitblasting/data/`).

### Table (custom suite, §4.1)

Raw data: `data/cvc5-custom-results.tsv` for cvc5 column; CBMC/Bitwuzla columns from manual runs.

### Table (SMT-COMP QF_BV community sample, §4.2)

Raw data: `data/cvc5-smt-comp-results.tsv` for cvc5; `data/smt-comp-results.tsv` for CBMC (mirror of Paper 1 data).
Benchmarks: `../../bench-multiplication/smt-comp-sample/*.smt2`.

### Table (SMT-LIB community set, §4.3)

Detailed category breakdown is available in the artifact. To re-run, use the
SMT-LIB 2023 submissions (GRS, p4dfa, UltimateAutomizer).

### Amulet comparison (§4.4)

We discuss Amulet at the level of use-case scope (gate-level vs SMT-BV).
A direct head-to-head time comparison is not meaningful because Amulet takes
AIG input and we take SMT-LIB input. The Amulet source is at
https://github.com/d-kfmnn/amulet2; build with `./configure.sh && make`.

## Mechanized Lean 4 proofs

Location: Lean files distributed with the artifact. The unit characterization
of `ZMod (2^d)` is also submitted as [Mathlib PR #38628](https://github.com/leanprover-community/mathlib4/pull/38628).

## Commit-to-claim mapping

- `features/adder` branch: paper, algebraic implementation, experiments
- See `doc/paper-algebraic/data/` for raw data

### Expression-level normalisation evaluation (§sec:future-within-and-beyond)

Raw data: `data/expr-norm-evaluation.tsv` (consolidated across three suites).

To re-run the simple-variant ablation:
```bash
bench-multiplication/run-expr-norm-ablation.sh    # custom suite (39, 30s)
bench-multiplication/run-expr-norm-martin.sh      # Martin subpoly (210, 10s)
# SMT-COMP sample (66, 30s) — inline loop, see commit history.
```

The variant is gated on `ENABLE_GB_EXPR_NORMALISE=1`; both runs use
this env var for the `expr_norm` column and an empty environment for
`default`.
