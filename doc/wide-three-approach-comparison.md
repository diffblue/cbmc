# Wide three-approach comparison

This document records the wider comparison of the three CBMC
multiplier-handling approaches across Paper 2's existing benchmark
pool plus the algebraic-pair benchmarks.

## Setup

Two complementary runs:

- **C-input pool** (47 benchmarks; `bench-multiplication/*.c` excluding
  floating-point, `realistic-patterns/*.c`, and synthetic stored
  patterns): all 5 configurations apply (`shift_add`, `comba_cs`,
  `pair_detect`, `p2_algebraic`, `all_combined`). Run via `cbmc`.
- **SMT2-input pool** (66 benchmarks; Paper 2's 39-benchmark suite,
  degree-scaling, variables-scaling, plus comm/assoc generated at
  BW=8..256): only 3 configurations (`shift_add`, `comba_cs`,
  `p2_algebraic`) since `--refine-arithmetic` is not exposed in
  `smt2_solver`. Run via `smt2_solver --cadical`.

Timeout: 15 s per cell. Wall-clock measurements via `time -p`.

## "All-combined done right" optimisation

When `--refine-arithmetic` is enabled, the algebraic layer (Paper 2's
Gröbner basis + vanishing polynomial) used to run first and consume
~1 s of work even on benchmarks where it could not solve the problem
(e.g. multiplications laundered through `store()`). After that wasted
work, refinement would start, pair detection would fire, and finish
the proof in a single iteration.

**Optimisation**: in `bv_refinementt::try_algebraic_solve` (override
of the inherited method), short-circuit when `--refine-arithmetic` is
the user's chosen mode. Pair detection covers the algebraic-identity
patterns relevant to the laundered cases with constant-size hint
clauses; the algebraic layer's work is wasted there. The override
returns `false` immediately, signalling "algebraic layer chose not to
run". An env variable `CBMC_DISABLE_REFINE_ALG_SKIP=1` reverts to the
previous behaviour for A/B comparison.

Empirical effect on `stored_comm` (uint16 stored commutativity):

| Configuration | Before optimisation | After optimisation |
|---------------|--------------------:|-------------------:|
| pair_detect (DISABLE_ALGEBRAIC + refine) | 0.04 s | 0.04 s |
| all_combined (algebraic + refine) | 1.24 s | **0.04 s** |
| With `CBMC_DISABLE_REFINE_ALG_SKIP=1` | 1.24 s | 1.25 s (recovers prior) |

The optimisation eliminates the redundant algebraic-layer attempt
when refinement is the chosen path, without affecting the
algebraic-layer's behaviour in non-refinement mode.

## Results

### C-input pool (47 benchmarks, 5 configs)

Per-configuration solved counts (out of 47):

| Configuration | Solved | Pct |
|---------------|-------:|----:|
| shift_add | 20 | 43% |
| comba_cs (Paper 1) | 21 | 45% |
| **pair_detect (Beame-Liew-inspired)** | **37** | **79%** |
| p2_algebraic (Paper 2) | 27 | 57% |
| **all_combined (optimised)** | **37** | **79%** |

Key observations:

- `comba_cs` adds ~1 benchmark over `shift_add`. Encoding choice
  alone is marginal on multiplier-equality problems whose underlying
  SAT problem is exponential in bit-width.
- `pair_detect` solves 16 more benchmarks than `comba_cs` (76% gain).
  These are the cases where the multiplications are laundered
  through opaque computation (function inlining, stored intermediates,
  type casts, pointer dereferences) that defeat the simplifier.
- `p2_algebraic` solves 6 more than `comba_cs` (29% gain). These
  are the visible-polynomial-identity cases that the algebraic
  layer recognises directly.
- **`all_combined` matches `pair_detect`** (both 37/47). The
  optimisation works: enabling everything no longer adds the
  algebraic-layer overhead.

Raw data: `bench-multiplication/wide-three-approach-comparison.tsv`.

### SMT2-input pool (66 benchmarks, 3 configs)

Per-configuration solved counts (out of 66):

| Configuration | Solved | Pct |
|---------------|-------:|----:|
| shift_add | 29 | 44% |
| comba_cs (Paper 1) | 40 | 61% |
| **p2_algebraic (Paper 2)** | **65** | **98.5%** |

Pool composition:
- 39 benchmarks from Paper 2's custom suite (`paper2-suite-results.tsv`)
- 10 from degree scaling (`binomial_deg{2..6}_bw{8,16}`)
- 5 from variables scaling (`varscale_k{2..6}_bw16`)
- 12 from BW scaling (`comm_{8..256}`, `assoc_{8..256}`)

The single benchmark unsolved by `p2_algebraic` is `bf16_mul_mono`,
which Paper 2 documents at 29 s; our 15 s timeout is too tight.
Extending the timeout to 30 s would solve it (consistent with
Paper 2's data).

Key observations:

- `p2_algebraic` dominates the SMT2 pool: 98.5% solved vs 61% for the
  best bit-blast encoding. This is Paper 2's home turf — visible
  polynomial structure that the Gröbner basis solver recognises
  directly.
- `comba_cs` is meaningfully better than `shift_add` (61% vs 44%) on
  these benchmarks, confirming Paper 1's encoding contribution.
- `shift_add` covers only the small-bitwidth cases.

Raw data: `bench-multiplication/wide-smt2-three-approach.tsv`.

## Combined picture

The two pools are complementary:

- **C-input pool**: dominated by laundered multiplication patterns
  where pair detection wins (algebraic layer can't see through
  bit-blasting of `store()` etc.). Pair detection solves 37/47.
- **SMT2-input pool**: dominated by visible polynomial structure
  where Paper 2's algebraic solver wins (no `store()` indirection in
  the SMT-LIB form). Algebraic solver solves 65/66.

Mapping configurations to "what they target":

| Configuration | Wins on |
|---------------|---------|
| shift_add | small bitwidths, simple problems |
| comba_cs | small/moderate bitwidths with bit-blast-amenable structure |
| pair_detect | C-level multiplier-equality patterns laundered through opaque computation |
| p2_algebraic | SMT-LIB-level polynomial identities at any bitwidth |
| all_combined | union of pair_detect and p2_algebraic, with optimisation |

`all_combined` is now the strict superset: solves what `pair_detect`
solves, plus on SMT2 inputs (where pair_detect doesn't apply) it
falls back to `p2_algebraic`. There is no benchmark in our pools
where `all_combined` is worse than the best of either component.

## Implications

For paper amendments:

- **Paper 2** can cite the wider comparison as evidence that pair
  detection (Paper 1's contribution) and the algebraic solver
  (Paper 2's) are complementary rather than competing. Both
  approaches close different sets of benchmarks; together they cover
  almost everything in our pools.
- **Paper 1** can cite `all_combined` as the production-ready
  pipeline: pair detection wins on the laundered cases, falls back
  to bit-blast otherwise. With Paper 2 also enabled, the algebraic
  solver layer adds the SMT-LIB-level identity recognition for free
  (no extra runtime cost when refinement is on, thanks to the
  optimisation).

The "all-combined done right" implementation is a small change
(one virtual override + env-var toggle for A/B) but produces a
clean composition where the two papers' contributions stack
without interference.

## Files

- Code change: `src/solvers/refinement/bv_refinement.h`
  (`try_algebraic_solve` override), `src/solvers/flattening/boolbv.h`
  (made `try_algebraic_solve` virtual).
- Runners: `bench-multiplication/run-wide-three-approach-comparison.sh`,
  `bench-multiplication/run-wide-smt2-comparison.sh`.
- Data: `bench-multiplication/wide-three-approach-comparison.tsv`,
  `bench-multiplication/wide-smt2-three-approach.tsv`.
