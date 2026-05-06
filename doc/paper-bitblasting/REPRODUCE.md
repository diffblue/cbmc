# Reproducing Paper 1 Results

This document describes how to reproduce the empirical results in the paper "Proof-Guided SAT Encoding Selection for Multiplication in Bounded Model Checking."

## Prerequisites

- Linux (tested on Ubuntu 24.04)
- CMake 3.8+, GCC 13+, Bison, Flex, Python 3.10+, `bc`
- Disk: ~5 GB for build, additional ~30 GB if running SMT-COMP comparison
- RAM: 8 GB minimum (experiments use `ulimit -v 6000000`)
- Standalone SAT solvers (optional, for cross-solver comparison):
  ```
  sudo apt-get install cryptominisat minisat
  ```

## Building CBMC with the encodings in this paper

```bash
git clone https://github.com/diffblue/cbmc.git
cd cbmc
git checkout features/adder    # the paper branch
git submodule update --init
cmake -S . -Bbuild -DCMAKE_BUILD_TYPE=Release
cmake --build build --target cbmc --target smt2_solver -- -j$(nproc)
```

The `smt2_solver` binary accepts the following encoding-related flags:
- `--multiplier-encoding {shift-add|comba|dadda|wallace|comba-cs|dadda-cs|booth|block4|sortnet}`
- `--adder-encoding {shift|bk|ks|sk|hc|lf}`

## Environment variables for ablation

| Variable | Effect | Used in |
|---|---|---|
| `DISABLE_SIMPLIFY=1` | Disable word-level simplification layer | Layer ablation (§7.2) |
| `DISABLE_ALGEBRAIC=1` | Disable Gröbner-basis algebraic solver | Layer ablation (§7.2) |
| `DISABLE_VANISHING=1` | Disable vanishing-polynomial test | Layer ablation (§7.2) |
| `FORCE_COMBA_CS_POPCOUNT=1` | Always use popcount path in combacs | Heuristic ablation (§5.1) |
| `FORCE_COMBA_CS_SHIFTADD=1` | Always fall back to shift-add in combacs | Heuristic ablation (§5.1) |
| `GROEBNER_REVERSE_ORDER=1` | Use reverse equation ordering in Gröbner | Ordering ablation (Paper 2) |
| `CBMC_PROOF_FILE=<path>` | Dump CaDiCaL DRAT proof to file | Proof analysis (§5) |
| `CBMC_DIMACS_FILE=<path>` | Dump SAT formula in DIMACS; skip solving | External solver comparison (§7.3) |

## Resource limits

All experiments should use:
```bash
ulimit -v 6000000      # 6 GB virtual memory cap
timeout -s 9 <sec> ... # wall-clock cap; SIGKILL on timeout
```

## Reproducing each table/figure

### Table 3: DRAT proof comparison (§5)

Raw data: `data/variance-5runs.tsv` (columns include proof statistics).

Re-run manually:
```bash
# For each encoding/benchmark pair:
env CBMC_PROOF_FILE=/tmp/proof.drat DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 \
    build/bin/smt2_solver --cadical --multiplier-encoding <enc> \
    bench-multiplication/smt-comp/comm_11.smt2
ls -l /tmp/proof.drat   # proof size in bytes
```

### Table 4: Booth vs shift-add sweep (§6.1)

Raw data: `data/booth-analysis.md`.

### Table: Layer ablation (§7.2)

Raw data: `data/layer-ablation.tsv`.

### Table: Heuristic ablation (§5.1)

Raw data: `data/heuristic-ablation.tsv`.

### Table: Variance (§7.4)

Raw data: `data/variance-5runs.tsv` (5 runs per pair).

### Scaling figure (§7.5)

Raw data: `data/scaling-results.tsv` (if present) or re-run:
```bash
for bw in 8 10 12 14 16 20 24 32; do
  for enc in shift-add comba comba-cs; do
    env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 \
        build/bin/smt2_solver --cadical --multiplier-encoding $enc \
        bench-multiplication/smt-comp/comm_${bw}.smt2
  done
done
```

## Benchmarks

All benchmarks are in `bench-multiplication/smt-comp/`. Categories:
- `comm_N.smt2`: commutativity at bit-width N
- `assoc_N.smt2`: associativity at bit-width N
- `distrib_N.smt2`: distributivity at bit-width N
- `const_mul_N_K.smt2`: constant multiplication `x*K == K*x` at bit-width N
- `strength_N_K.smt2`: strength reduction `x*K == (x<<k)-x` (or similar) at bit-width N
- `bf16_mul_comm_v2.smt2`: bfloat16 commutativity
- `mul_ineq_12.smt2`: inequality constraint
- `strength_chain_16.smt2`: three chained strength reductions
- `dot_product_8.smt2`, `mat_trace*.smt2`: matrix-style benchmarks

## External solver comparison

To reproduce the four-solver table:
```bash
# Dump DIMACS
env CBMC_DIMACS_FILE=/tmp/bench.dimacs DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 \
    build/bin/smt2_solver --cadical --multiplier-encoding comba-cs \
    bench-multiplication/smt-comp/comm_11.smt2

# Solve with each solver
cadical -q /tmp/bench.dimacs       # CaDiCaL
minisat /tmp/bench.dimacs /tmp/out # MiniSat
cryptominisat5 --verb 0 /tmp/bench.dimacs  # CryptoMiniSat
```

## Commit-to-claim mapping

- `features/adder` branch head: paper and all experiments
- `3ba9c6d17b`: Layer ablation and variance data
- `a48672360a`: Adaptive heuristic ablation (env vars added)
- See `doc/paper-bitblasting/data/` for raw experimental data

## Expected runtimes (Intel Xeon Platinum 8124M, 36 cores, 68 GB RAM)

- Build: ~5 minutes
- Layer ablation (12 benchmarks × 5 configs × 120s T/O): ~15 minutes
- Variance experiment (6 encodings × 25 benchmarks × 5 runs): ~1-2 hours
- Full multi-bitwidth scaling (8-64 bits × 3 encodings): ~30 minutes
- SMT-COMP QF_BV comparison (requires 30 GB disk): several hours
