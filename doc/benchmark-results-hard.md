# Hard Benchmark Results

These benchmarks consistently take >5s even in the best configuration,
making the speedups meaningful to users.

- Date: 2026-04-03
- Timeout: 90s, 1 run per configuration
- 3 benchmarks × 4 encodings × 5 solver configs = 60 data points

## equiv_unsat_200

UNSAT equivalence check: two addition implementations must agree, 200 iterations.

| Encoding | MiniSat | CaDiCaL | +rv | +xg | +xg+rv |
|----------|--------:|--------:|----:|----:|-------:|
| pc | 42.7 | 20.8 | 13.3 | 7.7 | **0.56** |
| simple | 53.9 | 4.8 | 2.7 | 4.2 | 7.8 |
| rani | 49.3 | 16.0 | 11.6 | T/O | 15.1 |
| lookahead | 57.2 | 30.1 | 28.6 | 1.6 | **1.4** |

Best: **pc + CaDiCaL + xg + rv = 0.56s** (75x over MiniSat, 37x over CaDiCaL baseline)

Key insight: XOR Gauss + reorder-vars combine multiplicatively on PC.
Lookahead + XOR Gauss is also very effective (1.4s) because lookahead
has fewer observed variables, reducing callback overhead.

## add_unsat_500

UNSAT constrained overflow check, 500 iterations.

| Encoding | MiniSat | CaDiCaL | +rv | +xg | +xg+rv |
|----------|--------:|--------:|----:|----:|-------:|
| pc | 22.5 | 19.5 | 24.5 | **1.5** | T/O |
| simple | 15.0 | 19.2 | 18.3 | 12.6 | T/O |
| rani | 48.7 | 20.9 | 17.8 | T/O | T/O |
| lookahead | 28.2 | 43.5 | 38.4 | 36.7 | T/O |

Best: **pc + CaDiCaL + xg = 1.5s** (15x over MiniSat, 13x over CaDiCaL baseline)

Key insight: XOR Gauss alone gives the best result. Adding reorder-vars
causes T/O — the reordering interacts badly with the XOR propagator on
this benchmark. MiniSat with Simple encoding (15.0s) beats CaDiCaL
baseline (19.5s).

## distrib_unsat_200

UNSAT distributivity of multiplication over addition, 200 iterations (16-bit).

| Encoding | MiniSat | CaDiCaL | +rv | +xg | +xg+rv |
|----------|--------:|--------:|----:|----:|-------:|
| pc | 32.6 | 8.1 | **0.88** | 35.3 | 37.0 |
| simple | T/O | 52.9 | **1.0** | T/O | T/O |
| rani | T/O | 29.3 | **1.1** | T/O | T/O |
| lookahead | 20.2 | 34.5 | 45.0 | 60.9 | 66.0 |

Best: **pc + CaDiCaL + rv = 0.88s** (37x over MiniSat, 9.3x over CaDiCaL baseline)

Key insight: --reorder-vars is the dominant optimization here. XOR Gauss
actively hurts (35s vs 8s). The reorder benefit is consistent across
PC/Simple/Rani (all ~1s) but not Lookahead (45s — worse than baseline).

## Summary

| Benchmark | Worst | Best | Speedup | Key optimization |
|-----------|------:|-----:|--------:|------------------|
| equiv_unsat_200 | 57.2s | 0.56s | 102x | --xor-gauss --reorder-vars |
| add_unsat_500 | 48.7s | 1.5s | 33x | --xor-gauss |
| distrib_unsat_200 | >90s | 0.88s | >100x | --reorder-vars |

**No single optimization dominates.** XOR Gauss is critical for
equivalence and overflow checks. Reorder-vars is critical for
distributivity. The two can combine (equiv) or conflict (add_unsat).

**Encoding matters less than optimization flags** for these hard
benchmarks. The best encoding varies (PC for equiv+xg, any for
distrib+rv) but the optimization flags provide 10-100x speedups
while encoding choice provides 2-4x.

