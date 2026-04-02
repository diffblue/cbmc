# Full Benchmark Matrix: Encoding × Solver × Optimizations

- Date: 2026-04-02
- Benchmarks: 12 synthetic C programs (24 SMT2 benchmarks omitted — all <0.001s)
- Runs: 2 per configuration, mean reported
- Timeout: 45s
- Metric: CaDiCaL/MiniSat solver time (seconds)
- Encodings: PC (propagation-complete ripple carry), Simple (simple ripple carry),
  Rani (MUX-based), Lookahead (carry lookahead)
- Optimizations: rv = --reorder-vars, xg = --xor-gauss

## pc encoding

| Benchmark              |       MiniSat |       CaDiCaL |    CaDiCaL+rv |    CaDiCaL+xg | CaDiCaL+xg+rv |
|------------------------|---------------|---------------|---------------|---------------|---------------|
| add_sat_200            |          0.27 |         0.008 |         0.021 |          0.35 |         0.039 |
| add_sat_2000           |          3.61 |          0.14 |          0.33 |           T/O |           T/O |
| add_unsat_200          |          3.85 |          5.70 |          5.75 |          0.50 |           T/O |
| chain_sat_500          |         0.038 |         0.067 |          0.30 |          3.32 |          5.49 |
| distrib_unsat_20       |          0.42 |          0.29 |         0.076 |          1.14 |          1.33 |
| equiv_unsat_100        |          6.62 |          7.78 |          4.37 |          0.46 |          0.43 |
| incr_sat_5000          |          0.82 |         0.061 |          0.47 |           T/O |           T/O |
| mixed_sat_500          |          9.72 |          1.34 |          0.53 |           T/O |          39.6 |
| narrow_sat_10000       |         <.001 |         <.001 |         0.008 |         <.001 |         0.018 |
| overflow_sat_200       |         0.074 |         0.064 |         0.019 |          1.65 |          2.80 |
| sub_sat_1000           |          13.7 |         0.034 |         0.033 |          13.7 |           T/O |
| wide_sat_1000          |          3.54 |          0.13 |          0.33 |           T/O |          36.1 |

## simple encoding

| Benchmark              |       MiniSat |       CaDiCaL |    CaDiCaL+rv |    CaDiCaL+xg | CaDiCaL+xg+rv |
|------------------------|---------------|---------------|---------------|---------------|---------------|
| add_sat_200            |          0.73 |         0.018 |         0.005 |          4.36 |          38.8 |
| add_sat_2000           |          31.0 |          0.25 |         0.064 |           T/O |           T/O |
| add_unsat_200          |          2.68 |          4.87 |          5.04 |          2.68 |          37.5 |
| chain_sat_500          |          0.57 |          0.14 |          0.17 |           T/O |           T/O |
| distrib_unsat_20       |          1.47 |          6.88 |         0.096 |          16.7 |          17.0 |
| equiv_unsat_100        |          9.38 |          1.88 |          1.54 |          1.23 |          1.67 |
| incr_sat_5000          |          1.16 |         0.076 |          0.60 |           T/O |           T/O |
| mixed_sat_500          |          13.2 |          1.09 |          13.8 |           T/O |           T/O |
| narrow_sat_10000       |         <.001 |         <.001 |         0.016 |           T/O |           T/O |
| overflow_sat_200       |         0.050 |         0.035 |         0.028 |          34.1 |           T/O |
| sub_sat_1000           |          13.6 |         0.056 |         0.051 |           T/O |           T/O |
| wide_sat_1000          |          38.7 |          0.24 |         0.061 |           T/O |           T/O |

## rani encoding

| Benchmark              |       MiniSat |       CaDiCaL |    CaDiCaL+rv |    CaDiCaL+xg | CaDiCaL+xg+rv |
|------------------------|---------------|---------------|---------------|---------------|---------------|
| add_sat_200            |          0.18 |         0.009 |         0.003 |          4.73 |           T/O |
| add_sat_2000           |          8.39 |          0.14 |         0.042 |           T/O |           T/O |
| add_unsat_200          |          8.45 |          5.40 |          5.37 |           T/O |          10.3 |
| chain_sat_500          |          0.15 |         0.067 |          0.11 |           T/O |           T/O |
| distrib_unsat_20       |          1.40 |          4.82 |         0.095 |          28.4 |          27.6 |
| equiv_unsat_100        |          7.13 |          1.24 |          1.24 |          1.05 |          1.46 |
| incr_sat_5000          |          0.82 |         0.069 |          0.50 |           T/O |           T/O |
| mixed_sat_500          |          25.4 |          12.9 |          5.16 |           T/O |           T/O |
| narrow_sat_10000       |         <.001 |         <.001 |         0.011 |           T/O |           T/O |
| overflow_sat_200       |          0.13 |         0.083 |         0.026 |          25.4 |           T/O |
| sub_sat_1000           |          1.79 |         0.026 |         0.033 |           T/O |           T/O |
| wide_sat_1000          |          8.51 |          0.14 |         0.042 |           T/O |           T/O |

## lookahead encoding

| Benchmark              |       MiniSat |       CaDiCaL |    CaDiCaL+rv |    CaDiCaL+xg | CaDiCaL+xg+rv |
|------------------------|---------------|---------------|---------------|---------------|---------------|
| add_sat_200            |          0.28 |         0.015 |         0.011 |         0.007 |         0.015 |
| add_sat_2000           |          2.92 |          0.18 |          0.12 |          0.16 |          0.30 |
| add_unsat_200          |          4.87 |          14.8 |          10.5 |           T/O |           T/O |
| chain_sat_500          |          0.32 |         0.064 |         0.044 |           T/O |          4.84 |
| distrib_unsat_20       |          0.97 |          5.64 |          5.76 |          2.39 |          2.78 |
| equiv_unsat_100        |          8.95 |          14.0 |          9.43 |           T/O |           T/O |
| incr_sat_5000          |          0.56 |         0.043 |          0.54 |          4.07 |          4.35 |
| mixed_sat_500          |          15.1 |          1.40 |          10.1 |          12.4 |          13.0 |
| narrow_sat_10000       |         <.001 |         <.001 |         0.010 |         <.001 |         0.010 |
| overflow_sat_200       |         0.032 |         0.080 |         0.020 |          2.79 |          8.25 |
| sub_sat_1000           |           T/O |         0.025 |         0.032 |          14.0 |          14.9 |
| wide_sat_1000          |          2.74 |          0.17 |          0.12 |         0.085 |          0.19 |

## MiniSat (all encodings)

| Benchmark              |         pc |     simple |       rani |  lookahead |
|------------------------|------------|------------|------------|------------|
| add_sat_200            |       0.27 |       0.73 |       0.18 |       0.28 |
| add_sat_2000           |       3.61 |       31.0 |       8.39 |       2.92 |
| add_unsat_200          |       3.85 |       2.68 |       8.45 |       4.87 |
| chain_sat_500          |      0.038 |       0.57 |       0.15 |       0.32 |
| distrib_unsat_20       |       0.42 |       1.47 |       1.40 |       0.97 |
| equiv_unsat_100        |       6.62 |       9.38 |       7.13 |       8.95 |
| incr_sat_5000          |       0.82 |       1.16 |       0.82 |       0.56 |
| mixed_sat_500          |       9.72 |       13.2 |       25.4 |       15.1 |
| narrow_sat_10000       |      <.001 |      <.001 |      <.001 |      <.001 |
| overflow_sat_200       |      0.074 |      0.050 |       0.13 |      0.032 |
| sub_sat_1000           |       13.7 |       13.6 |       1.79 |        T/O |
| wide_sat_1000          |       3.54 |       38.7 |       8.51 |       2.74 |

## CaDiCaL (all encodings)

| Benchmark              |         pc |     simple |       rani |  lookahead |
|------------------------|------------|------------|------------|------------|
| add_sat_200            |      0.008 |      0.018 |      0.009 |      0.015 |
| add_sat_2000           |       0.14 |       0.25 |       0.14 |       0.18 |
| add_unsat_200          |       5.70 |       4.87 |       5.40 |       14.8 |
| chain_sat_500          |      0.067 |       0.14 |      0.067 |      0.064 |
| distrib_unsat_20       |       0.29 |       6.88 |       4.82 |       5.64 |
| equiv_unsat_100        |       7.78 |       1.88 |       1.24 |       14.0 |
| incr_sat_5000          |      0.061 |      0.076 |      0.069 |      0.043 |
| mixed_sat_500          |       1.34 |       1.09 |       12.9 |       1.40 |
| narrow_sat_10000       |      <.001 |      <.001 |      <.001 |      <.001 |
| overflow_sat_200       |      0.064 |      0.035 |      0.083 |      0.080 |
| sub_sat_1000           |      0.034 |      0.056 |      0.026 |      0.025 |
| wide_sat_1000          |       0.13 |       0.24 |       0.14 |       0.17 |

## CaDiCaL+rv (all encodings)

| Benchmark              |         pc |     simple |       rani |  lookahead |
|------------------------|------------|------------|------------|------------|
| add_sat_200            |      0.021 |      0.005 |      0.003 |      0.011 |
| add_sat_2000           |       0.33 |      0.064 |      0.042 |       0.12 |
| add_unsat_200          |       5.75 |       5.04 |       5.37 |       10.5 |
| chain_sat_500          |       0.30 |       0.17 |       0.11 |      0.044 |
| distrib_unsat_20       |      0.076 |      0.096 |      0.095 |       5.76 |
| equiv_unsat_100        |       4.37 |       1.54 |       1.24 |       9.43 |
| incr_sat_5000          |       0.47 |       0.60 |       0.50 |       0.54 |
| mixed_sat_500          |       0.53 |       13.8 |       5.16 |       10.1 |
| narrow_sat_10000       |      0.008 |      0.016 |      0.011 |      0.010 |
| overflow_sat_200       |      0.019 |      0.028 |      0.026 |      0.020 |
| sub_sat_1000           |      0.033 |      0.051 |      0.033 |      0.032 |
| wide_sat_1000          |       0.33 |      0.061 |      0.042 |       0.12 |

## CaDiCaL+xg (all encodings)

| Benchmark              |         pc |     simple |       rani |  lookahead |
|------------------------|------------|------------|------------|------------|
| add_sat_200            |       0.35 |       4.36 |       4.73 |      0.007 |
| add_sat_2000           |        T/O |        T/O |        T/O |       0.16 |
| add_unsat_200          |       0.50 |       2.68 |        T/O |        T/O |
| chain_sat_500          |       3.32 |        T/O |        T/O |        T/O |
| distrib_unsat_20       |       1.14 |       16.7 |       28.4 |       2.39 |
| equiv_unsat_100        |       0.46 |       1.23 |       1.05 |        T/O |
| incr_sat_5000          |        T/O |        T/O |        T/O |       4.07 |
| mixed_sat_500          |        T/O |        T/O |        T/O |       12.4 |
| narrow_sat_10000       |      <.001 |        T/O |        T/O |      <.001 |
| overflow_sat_200       |       1.65 |       34.1 |       25.4 |       2.79 |
| sub_sat_1000           |       13.7 |        T/O |        T/O |       14.0 |
| wide_sat_1000          |        T/O |        T/O |        T/O |      0.085 |

## CaDiCaL+xg+rv (all encodings)

| Benchmark              |         pc |     simple |       rani |  lookahead |
|------------------------|------------|------------|------------|------------|
| add_sat_200            |      0.039 |       38.8 |        T/O |      0.015 |
| add_sat_2000           |        T/O |        T/O |        T/O |       0.30 |
| add_unsat_200          |        T/O |       37.5 |       10.3 |        T/O |
| chain_sat_500          |       5.49 |        T/O |        T/O |       4.84 |
| distrib_unsat_20       |       1.33 |       17.0 |       27.6 |       2.78 |
| equiv_unsat_100        |       0.43 |       1.67 |       1.46 |        T/O |
| incr_sat_5000          |        T/O |        T/O |        T/O |       4.35 |
| mixed_sat_500          |       39.6 |        T/O |        T/O |       13.0 |
| narrow_sat_10000       |      0.018 |        T/O |        T/O |      0.010 |
| overflow_sat_200       |       2.80 |        T/O |        T/O |       8.25 |
| sub_sat_1000           |        T/O |        T/O |        T/O |       14.9 |
| wide_sat_1000          |       36.1 |        T/O |        T/O |       0.19 |

## Best configuration per benchmark

| Benchmark              | Best Config               |     Time |  vs PC/CaDiCaL |
|------------------------|---------------------------|----------|----------------|
| add_sat_200            | rani/CaDiCaL+rv           |    0.003 |           2.6x |
| add_sat_2000           | rani/CaDiCaL+rv           |    0.042 |           3.2x |
| add_unsat_200          | pc/CaDiCaL+xg             |     0.50 |          11.4x |
| chain_sat_500          | pc/MiniSat                |    0.038 |           1.8x |
| distrib_unsat_20       | pc/CaDiCaL+rv             |    0.076 |           3.7x |
| equiv_unsat_100        | pc/CaDiCaL+xg+rv          |     0.43 |          17.9x |
| incr_sat_5000          | lookahead/CaDiCaL         |    0.043 |           1.4x |
| mixed_sat_500          | pc/CaDiCaL+rv             |     0.53 |           2.5x |
| narrow_sat_10000       | lookahead/MiniSat         |    <.001 |              — |
| overflow_sat_200       | pc/CaDiCaL+rv             |    0.019 |           3.5x |
| sub_sat_1000           | lookahead/CaDiCaL         |    0.025 |           1.4x |
| wide_sat_1000          | rani/CaDiCaL+rv           |    0.042 |           3.1x |

## Geometric mean speedup over MiniSat (per encoding)

### pc
- CaDiCaL           6.21x (11 benchmarks)
- CaDiCaL+rv        5.06x (11 benchmarks)
- CaDiCaL+xg        0.56x (7 benchmarks)
- CaDiCaL+xg+rv     0.28x (7 benchmarks)

### simple
- CaDiCaL          10.16x (11 benchmarks)
- CaDiCaL+rv       14.47x (11 benchmarks)
- CaDiCaL+xg        0.18x (5 benchmarks)
- CaDiCaL+xg+rv     0.16x (4 benchmarks)

### rani
- CaDiCaL           6.57x (11 benchmarks)
- CaDiCaL+rv       12.24x (11 benchmarks)
- CaDiCaL+xg        0.09x (4 benchmarks)
- CaDiCaL+xg+rv     0.59x (3 benchmarks)

### lookahead
- CaDiCaL           2.93x (10 benchmarks)
- CaDiCaL+rv        2.67x (10 benchmarks)
- CaDiCaL+xg        1.52x (7 benchmarks)
- CaDiCaL+xg+rv     0.66x (8 benchmarks)

## Key Findings

1. **CaDiCaL baseline is 3-10x faster than MiniSat** across all encodings
   (geometric mean). The gap is largest for Simple (10x) and smallest for
   Lookahead (3x).

2. **--reorder-vars helps CaDiCaL on Simple and Rani** (14x and 12x over
   MiniSat respectively), making them competitive with PC. For PC itself,
   reorder-vars slightly reduces the geomean (6.2x to 5.1x) due to clause
   buffering overhead on easy benchmarks, but gives large wins on hard ones
   (distrib_unsat: 0.29s→0.076s, equiv_unsat: 7.8s→4.4s, mixed: 1.3s→0.5s).

3. **--xor-gauss is only effective with PC and Lookahead encodings.**
   With Simple and Rani, it causes widespread T/O. With PC, it gives
   dramatic UNSAT speedups (add_unsat 11x, equiv_unsat 18x) but hurts SAT.
   With Lookahead, it's surprisingly effective on SAT (add_sat_200: 0.007s)
   because the encoding has fewer XOR variables to observe.

4. **MiniSat wins on chain_sat_500** (0.038s vs 0.067s CaDiCaL) and
   **add_unsat_200** (3.85s vs 5.70s CaDiCaL). These are the only two
   benchmarks where MiniSat beats CaDiCaL baseline.

5. **Lookahead encoding is uniquely good with --xor-gauss** because it
   has no explicit carry variables, so fewer XOR constraints are registered,
   reducing observer callback overhead. It's the only encoding where
   --xor-gauss doesn't cause widespread T/O on SAT benchmarks.

6. **Recommended configurations:**
   - Default: PC + CaDiCaL (most robust, 6.2x over MiniSat)
   - UNSAT-heavy: PC + CaDiCaL + --xor-gauss (11-18x on UNSAT)
   - SAT-heavy with many additions: Rani + CaDiCaL + --reorder-vars
   - Mixed workload: PC + CaDiCaL + --reorder-vars (best on distrib, mixed, overflow)
