# Experimental Findings from Background Experiments (2026-05-06)

## Experiment 1: Bitwidth Scaling — Gröbner Basis is bitwidth-independent

**Hypothesis:** Algebraic solver time is independent of bitwidth
(polynomial equality commutes over Z_{2^d} regardless of d).

**Method:** Ran commutativity and associativity checks at bitwidths
8, 16, 32, 64, 128, 256 (commutativity also 256), 5 runs each.

**Result:** Strong confirmation of bitwidth independence.

| Benchmark | BW=8 | BW=16 | BW=32 | BW=64 | BW=128 | BW=256 |
|-----------|------|-------|-------|-------|--------|--------|
| commutativity | 4.8 ± 0.4 ms* | 4.7 ± 0.1 ms | 4.7 ± 0.1 ms | 4.8 ± 0.1 ms | 4.7 ± 0.02 ms | 4.7 ± 0.1 ms |
| associativity | 4.9 ± 0.4 ms | 4.7 ± 0.1 ms | 4.7 ± 0.06 ms | 4.7 ± 0.05 ms | 4.7 ± 0.04 ms | — |

*BW=8 had one outlier of 50ms (first run, likely initialization).

**Interpretation:** Bitwidth independence is REAL and clearly demonstrated.
From BW=8 to BW=256 (32× bitwidth increase), time is unchanged.
This is the most convincing scaling result for algebraic approach.

## Experiment 2: Equation Ordering Ablation — 2000× claim NOT supported

**Hypothesis:** The paper claims equation ordering (definitions before
Rabinowitsch) gives 2000× speedup vs reverse ordering.

**Method:** Ran 6 benchmarks with normal vs reverse ordering, 3 runs each.

**Result:** Within 5-15% for all benchmarks; reverse is actually *slightly
faster* on these.

| Benchmark | Normal | Reverse | Ratio |
|-----------|--------|---------|-------|
| comm_8 | 6.5 ms | 5.5 ms | 0.85× |
| comm_16 | 5.8 ms | 5.3 ms | 0.91× |
| comm_32 | 5.6 ms | 5.4 ms | 0.96× |
| assoc_8 | 5.9 ms | 5.5 ms | 0.95× |
| distrib_8 | 5.8 ms | 5.4 ms | 0.92× |
| overflow_detect_16 | 8.7 ms | 8.2 ms | 0.94× |

**Interpretation:** CRITICAL FINDING — the 2000× claim in the paper
is NOT supported by this experiment. Possible explanations:

1. Word-level simplification is handling these before Gröbner runs
   (most polynomial equalities become `true` via simplification).
2. The 2000× applied during early development before other optimizations.
3. The 2000× applies only to specific benchmark patterns we haven't tested.

**Action required:** Either (a) find a benchmark where 2000× holds, or
(b) retract the claim. Current claim is unsupported.

## Experiment 3: Layer Ablation (IN PROGRESS)

Running 5 configurations × 12 benchmarks. Will show:
- What does 1 layer (shift-add only) solve?
- What does each additional layer add?
- Which benchmarks require which layer?
