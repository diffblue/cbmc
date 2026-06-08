# Algebraic-pair detection in CBMC's `--refine-arithmetic`

This document is the comprehensive technical record of the algebraic-pair
detection contribution to CBMC's bit-vector refinement loop. It is
intended as source material for paper amendments and as a reference for
future work. Pin commit on `features/adder` covering the work:
`f92193c5d1` (final commit) up to `211a1f2df3` (first detection commit).

Sections:
1. Motivation
2. Technique
3. Implementation
4. Experimental methodology
5. Empirical scaling
6. Comparison study
7. Algebraic identity coverage
8. Regression validation
9. Real-world patterns
10. Where pair detection does not help
11. Future work
12. File index for reproducibility

## 1. Motivation

CBMC's `--refine-arithmetic` flag enables a refinement loop that lazily
approximates each multiplication with weak axioms (`x*0 = 0`, `x*1 = x`)
and progressively adds stronger constraints when the SAT solver returns
a spurious counterexample. Existing modes (selected at compile time
via `REFINE_MULT_MODE`):

- 0: full multiplier on first spurious counterexample.
- 1 (default): narrow multiplier (low 4 bits exact, high free) first,
  then full.
- 2 / 3: Karatsuba / Toom-Cook polynomial-evaluation refinements.

These modes refine *one multiplication at a time* and are blind to
algebraic relationships *between* multiplications. The CBMC expression
simplifier handles surface algebraic identities (`a*b == b*a`,
`a*(b+c) == a*b + a*c`, etc.) at the syntactic level, but it cannot see
through value-laundering operations: opaque function calls, array
stores and loads, pointer dereferences, type casts, or SSA copies that
arise from function inlining. After such operations, the multiplications
are bit-blasted independently and the SAT solver must rediscover the
algebraic equivalence by exhaustive bit-level search — exponential in
the operand bit-width.

Beame & Liew (2017) showed that array-multiplier commutativity has a
polynomial-size resolution refutation. The N3 work in
`bench-multiplication/n3-beame-liew/` reproduces that proof empirically
and produces DRAT certificates of the polynomial bound. The present
contribution applies the same insight at a different level of CBMC's
machinery: at the bit-vector refinement layer, where it is structurally
trivial to detect commutative / associative / distributive pairs of
multiplication approximations and short-circuit the SAT solver's
rediscovery work with a single equality assertion.

The contribution is small in code (≈120 lines) but produces dramatic
empirical improvements on multiplier-equality patterns that arise
naturally in real verification problems. It is sound by construction
(the asserted equality holds for any bit-vector type), it is silent on
problems without the target pattern (no overhead), and it composes with
the existing `--refine-arithmetic` machinery without any other change.

## 2. Technique

### 2.1 Pattern detection

The detector runs once after `finish_eager_conversion()` in
`bv_refinementt::dec_solve` and walks the list of approximations
(`mult_exprt`s the refinement layer is tracking).

For each multiplication approximation `m`, compute a **flat factor
multiset** by recursively descending two ways:

1. Through `mult_exprt` sub-expressions (commutativity / associativity:
   `mult(a, mult(b, c))` yields factors `{a, b, c}`).
2. Through operand bit-vectors that match another approximation's
   `result_bv` (the BV-level link: when intermediate products have
   been laundered through stored values, function calls, or pointer
   dereferences, the operand expression is a fresh symbol but the
   bit-vector is still equal to the inner approximation's result;
   recovering this link yields the original operand structure).

Two multiplications with equal flat factor multisets must produce equal
bit-vector results modulo `2^n`, since integer multiplication is both
commutative and associative.

For distributivity, an additional pass: for each multiplication
`m = mult(f, plus(p, q))` (with operand swap also accepted), search for
two other multiplications `m_p ≈ mult(f, p)` and `m_q ≈ mult(f, q)`. If
both exist, assert `m.result_bv == m_p.result_bv + m_q.result_bv`.

### 2.2 BV-level operand resolution

The recursive descent for operand BV identity is the key trick that
catches function-inlined cases. CBMC's bit-blast layer produces fresh
auxiliary variables for each shift / xor / arithmetic operation, but
multiplication results are stored as `result_bv` in the approximation
record. The detector indexes `result_bv -> approximation*` and uses
this index to follow operand bit-vectors back to the multiplication
they came from.

Because plus is bit-blasted directly (not approximated), distributivity
cannot use the same BV-level recursion through additions. The
distributivity branch therefore relies on the expression-level
`plus_exprt` shape being visible directly, which is a more restrictive
match. Extending it to track addition results would be future work.

### 2.3 Soundness

The asserted equalities are:

- `m1.result_bv == m2.result_bv` when `m1` and `m2` have equal flat
  factor multisets. Sound because integer (or unsigned) multiplication
  is commutative and associative modulo `2^n` for any `n`.
- `m_dist.result_bv == m_p.result_bv + m_q.result_bv` when
  `m_dist = mult(f, plus(p, q))`, `m_p ≈ mult(f, p)`, `m_q ≈ mult(f, q)`.
  Sound by distributivity of bit-vector multiplication over addition.

Both equalities are constant-size (one bit per output position plus the
per-bit equality clause) and are emitted before the refinement loop
begins. They cannot introduce spurious models because they hold under
all valid operand assignments.

## 3. Implementation

### 3.1 Files modified

- `src/solvers/refinement/bv_refinement.h`: added `detect_algebraic_pairs`
  to the public method list.
- `src/solvers/refinement/bv_refinement_loop.cpp`: invoke
  `detect_algebraic_pairs()` once in `dec_solve` immediately after
  `finish_eager_conversion()`.
- `src/solvers/refinement/refine_arithmetic.cpp`: implementation of
  `detect_algebraic_pairs` (≈120 lines).
- `src/solvers/refinement/refine_arithmetic.cpp`: experimental
  `REFINE_MULT_MODE = 4` adaptive-prefix refinement (not enabled by
  default; documented as a stepping stone in
  `doc/beame-liew-refinement.md`).

### 3.2 Runtime toggle

Environment variable `CBMC_DISABLE_REFINE_PAIR_DETECTION=1` disables the
detector at runtime. This was used for all A/B comparisons in this
study and is also useful for diagnosing whether a regression involves
pair detection. The toggle has no effect when `--refine-arithmetic` is
not set.

### 3.3 Logging

The detector emits one `BV-Refinement: detected N commutative/associative
multiplier pair(s)` message per `dec_solve` call when at least one pair
is found, and a separate message for distributive triples. This is the
mechanism by which we count detections in the experimental tables
below.

## 4. Experimental methodology

All experiments run on Linux x86_64 with:

- CBMC built from `features/adder` branch at commit `f92193c5d1` (or
  later) with `cmake --build build --target cbmc`.
- `ulimit -v 57591731` (about 80% of the 68 GB system memory).
- `timeout` per experiment as documented in each section.
- 30 s default timeout for benchmarks unless otherwise noted.
- Each timing taken from a single run; T/O denotes the imposed timeout.

All scripts and TSV data live in `bench-multiplication/`. The original
benchmark suite (`comm.c`, `mod_mul.c`, `widen_mul.c`, ...) is from
`features/adder` and predates this contribution. New artifacts:

- `run-pair-detection-scaling.sh`, `scaling-pair-detection.tsv`: §5.
- `run-distributivity-scaling.sh`, `scaling-distributivity.tsv`: §5.
- `comparison-study.tsv`: §6.
- `sv-comp-results.tsv`: §9.
- `auto-large-results.tsv`: §9.
- `realistic-patterns/p*.c`, `realistic-patterns/results.tsv`: §9.

## 5. Empirical scaling

The empirical scaling study at varying operand bit-widths produces a
clear **polynomial-vs-exponential signature**: time-to-verify grows
roughly polynomially with bit-width when pair detection is enabled and
roughly exponentially when it is not.

### 5.1 Commutativity-style scaling

Patterns: four pair-detection-amenable patterns
(`run-pair-detection-scaling.sh`, 180 s timeout):

- `widen_mul`: `(uint{2N})a * (uint{2N})b == (uint{2N})b * (uint{2N})a`
  where the cast prevents the simplifier's expression-level
  commutativity rule.
- `stored_widen`: same product flowed through `store(...)` opaque.
- `three_term_widen`: `a*x + b*y + c*z` reordered with all per-term
  swaps.
- `assoc_widen`: `(a*b)*c == a*(b*c)` through stored intermediates.

| W | widen_mul (with / without) | stored_widen | three_term_widen | assoc_widen |
|--:|---:|---:|---:|---:|
| 4 | 0.03 / 0.05 | 1.17 / 1.18 | 0.07 / 2.60 | 1.20 / 1.60 |
| 6 | 0.03 / 0.25 | 1.16 / 1.43 | 0.06 / T/O | 1.20 / T/O |
| 8 | 0.03 / 21.72 | 1.16 / 13.63 | 0.05 / T/O | 1.20 / T/O |
| 10 | 0.03 / T/O | 1.22 / T/O | 0.09 / T/O | 1.27 / T/O |
| 12 | 0.03 / T/O | 1.23 / T/O | 0.09 / T/O | 1.27 / T/O |
| 14 | 0.03 / T/O | 1.22 / T/O | 0.09 / T/O | 1.26 / T/O |
| 16 | 0.03 / T/O | 1.22 / T/O | 0.09 / T/O | 1.26 / T/O |
| 20 | 0.03 / T/O | 1.33 / T/O | 0.19 / T/O | 1.38 / T/O |
| 24 | 0.03 / T/O | 1.33 / T/O | 0.17 / T/O | 1.38 / T/O |
| 28 | 0.03 / T/O | 1.34 / T/O | 0.16 / T/O | 1.39 / T/O |
| 32 | 0.03 / T/O | 1.33 / T/O | 0.16 / T/O | 1.38 / T/O |

Without pair detection, `widen_mul` already times out at 10 bits; the
other three patterns time out at 8-10 bits. With pair detection every
pattern stays under 2 s through 32 bits. The 1.17-1.39 s baseline for
`stored_widen` and `assoc_widen` is the under-approximation refinement
overhead in CBMC's loop, not the multiplier proof.

### 5.2 Distributivity scaling

(`run-distributivity-scaling.sh`, 180 s timeout, pattern
`a*(b+c) == a*b + a*c` through stored intermediates.)

| W | with pair detection | without pair detection |
|--:|--------------------:|-----------------------:|
| 4 | 15.85 s | 16.12 s |
| 6 | 15.84 s | 133.90 s |
| 8 | 15.93 s | T/O |
| 10 | 16.09 s | T/O |
| 12 | 16.07 s | T/O |
| 14 | 16.14 s | T/O |
| 16 | 16.12 s | T/O |
| 20 | 16.66 s | T/O |
| 24 | 16.71 s | T/O |
| 32 | 16.70 s | T/O |

The distributivity baseline (16 s) is higher than commutativity
(1.2 s) because the right-hand side `m_p.result_bv + m_q.result_bv`
involves an additional bit-blasted adder. Time still stays roughly
constant in bit-width with pair detection while exploding without.

### 5.3 Polynomial-vs-exponential

For each pattern in §5.1 / §5.2 the time series with pair detection
stays bounded; without it the time series enters the timeout regime by
roughly 8-12 bits. This is the empirical signature of a polynomial-size
proof witness short-circuiting an exponential-time CDCL search.

## 6. Comparison study

A/B comparison across alternative SAT/SMT configurations on a fixed
benchmark set (`comparison-study.tsv`, 30 s timeout):

| Benchmark | default CBMC | --refine + pair | --refine no-pair | --xor-gauss | CryptoMiniSat | Bitwuzla |
|-----------|---:|---:|---:|---:|---:|---:|
| stored_comm | T/O | **1.23 s** | T/O | T/O | T/O | 0.03 s |
| stored_comm32 | T/O | **1.37 s** | T/O | T/O | T/O | 0.03 s |
| sub_comm | 0.03 | 0.03 | 0.03 | 0.03 | 0.04 | 0.03 |
| assoc_stored | T/O | **1.38 s** | T/O | T/O | T/O | 0.03 s |
| distrib_simple | T/O | **16.66 s** | T/O | T/O | T/O | 0.03 s |
| widen_mul | T/O | **0.03 s** | T/O | T/O | T/O | 0.03 s |
| mod_mul | 5.24 | **1.47 s** | 4.89 | 5.22 | 16.61 | 0.03 s |
| comm | 0.03 | 0.03 | 0.03 | 0.03 | 0.03 | 0.03 |
| distrib | 0.02 | 0.03 | 0.03 | 0.03 | 0.03 | 0.03 |
| assoc | 1.25 | 1.26 | 1.26 | 1.25 | 1.25 | 0.04 |
| hash_mul | T/O | T/O | T/O | T/O | T/O | 0.03 s |
| mac_equiv | 0.03 | 0.03 | 0.03 | 0.03 | 0.04 | 0.03 |
| matrix_mul | 0.03 | 0.03 | 0.03 | 0.03 | 0.04 | 0.03 |
| matrix_trace_16 | 0.04 | 0.03 | 0.03 | 0.04 | 0.06 | 0.03 |

Reading:

- **Bitwuzla** wins everywhere because its word-level reasoning sees
  through algebraic identities directly without bit-blasting. It is
  the best-case oracle for these problems.
- **Pair detection** on top of `--refine-arithmetic` brings CBMC's
  bit-blasted regime as close to Bitwuzla as is structurally possible.
  The remaining gap (1.2-1.4 s typical, 16 s for distributivity) is
  the under-approximation refinement loop, not the multiplier proof.
- **`--xor-gauss` and CryptoMiniSat** target the linear (XOR) part of
  bit-blasted arithmetic and do not help on multiplier AND-trees.
  CryptoMiniSat is occasionally slower (mod_mul) than CBMC default,
  illustrating that GF(2) Gaussian elimination is not the right tool
  for non-XOR problems.
- **`hash_mul`** times out for all CBMC modes because pair detection
  does not see through SSA/CSE renaming of the same arithmetic chain;
  Bitwuzla solves it trivially via word-level reasoning. This is the
  primary unsolved case among CBMC modes.

## 7. Algebraic identity coverage

The detector handles the following identities natively:

| Identity | Detection mechanism | Empirical example |
|----------|---------------------|-------------------|
| Commutativity (`a*b == b*a`) | Flat factor multiset equality | `widen_mul` (T/O → 0.03 s at W=32) |
| CSE (`a*b == a*b` with renamed SSA) | Same as commutativity (single-element case) | Captured by the detector but not exercised explicitly in benchmarks |
| Associativity (`(a*b)*c == a*(b*c)`) | Recursive flattening through mult sub-expressions and BV-level operand resolution | `assoc_stored` (T/O → 1.39 s at W=32) |
| Distributivity (`a*(b+c) == a*b + a*c`) | Pattern match on `mult(f, plus(p, q))` with companion mult lookup | `distrib_simple` (T/O → 16.7 s at W=32) |
| Multi-factor compositions of the above | Flat factor multiset propagates compositionally | `three_term_widen` (3 pairs detected) |

Patterns NOT handled (future work):

- Distributivity through opaque-stored sums: `mult(f, store(plus(p, q)))`
  would require tracking addition results at the BV level. Would catch
  the `p7_bitmix_distrib.c` and similar patterns.
- Same-input deterministic chains (`hash(a) == hash(a)` after function
  inlining): would require either expression-level SSA-aware
  comparison or a bit-blast cache.
- Negation identities (`(-a) * (-b) == a*b`): a small extension of
  pattern matching, not yet implemented.
- More complex algebraic identities (`a*a + 2*a*b + b*b == (a+b)^2`):
  requires identity-specific patterns or a more general algebraic
  preprocessor.

## 8. Regression validation

### 8.1 Targeted regression tests

Two new tests added to `regression/cbmc-incr-oneloop/`:

- `multiply-stored-pairs-refine`: stored commutativity + subtractive
  commutativity + stored associativity through opaque store. Without
  pair detection these time out at uint16; with pair detection each
  is dispatched in seconds.
- `multiply-distributivity-refine`: stored distributivity through
  opaque store. Same characteristic.

The pre-existing test
`regression/cbmc-incr-oneloop/multiply-correctness-refine/main.c`
exercises both narrow and wide multiplications including a uint8
commutativity check. Pair detection takes it from 2.68 s to 0.21 s
(13x speed-up).

### 8.2 Broader sweep

Random samples of CBMC's main `regression/cbmc/` suite, run once with
and once without pair detection (`--refine-arithmetic` enabled in both
modes, so any difference is attributable to the detector):

| Sample size | with-pair pass | without-pair pass | differ |
|-------------|---------------:|------------------:|-------:|
| 100 | 93/93 (7 had no test.desc) | 93/93 | 0 |
| 200 | 164/165 (1 missing main.c) | 164/165 | 0 |

In each case, every test produced identical pass/fail outcome with and
without pair detection. The one failure was consistent across modes
and not attributable to the detector. Wall-clock times for the test
runner are 24-38 s for the full sweep; pair detection adds no
measurable per-test overhead on benchmarks where it does not fire.

The full `regression/cbmc-incr-oneloop/` suite (41 tests) and the
`regression/cbmc/Array_UF{1..10,15,20}` suite (12 tests) all pass.

## 9. Real-world patterns

### 9.1 SV-COMP

Sampled from cloned `sosy-lab/sv-benchmarks` repository (`sv-comp.org`).
30 files each from `c/bitvector/`, `c/loops/`, `c/float-newlib/`, plus
inspection of `c/array-multidimensional/` and `c/array-examples/`.

| Category | Files sampled | Pair detection fires | Helps | Hurts | Same |
|----------|--------------:|---------------------:|------:|------:|-----:|
| bitvector | 30 | 0 | 0 | 0 | 30 |
| loops | 30 | 0 | 0 | 0 | 30 |
| float-newlib | 20 | 0 | 0 | 0 | 20 |

The SV-COMP categories surveyed do not contain multiplier-equality
patterns. SV-COMP `bitvector` emphasises bit operations (XOR, shifts,
masks) and rarely uses multiplication between two non-constant values;
`loops` and `float-newlib` likewise have arithmetic but not commuting
products. Pair detection has zero hit rate, no time difference. This
documents the *targeting* of the technique: it is silent on
benchmarks that are not algebraic-multiplier problems.

### 9.2 CBMC's `--auto-large` benchmarks

CBMC's `scripts/profile_cbmc.py --auto-large` generates 10 standard
benchmarks (linked_list, array_ops, structs, dlinked_list, string_ops,
func_ptrs, bitvector, matrix, unions, tree). Run each with
`--refine-arithmetic` + the standard args (`--bounds-check`,
`--unwind`, etc):

| Benchmark | with pair | with_pairs | without pair |
|-----------|----------:|----------:|-------------:|
| bitvector | 0.04 | 0 | 0.04 |
| dlinked_list | 2.30 | 0 | 2.30 |
| tree | 26.92 | 0 | 26.97 |
| linked_list | 1.22 | 0 | 1.21 |
| structs | 0.10 | 0 | 0.11 |
| func_ptrs | 0.04 | 0 | 0.04 |
| array_ops | T/O | 0 | T/O |
| matrix | 1.71 | 0 | 1.74 |
| unions | 0.07 | 0 | 0.07 |
| string_ops | 0.33 | 0 | 0.34 |

Pair detection fires zero times on these benchmarks. Same conclusion
as SV-COMP: the standard CBMC benchmark suite does not contain
multiplier-equality patterns.

### 9.3 Realistic synthetic patterns

To document where the technique *does* help, we constructed eight
patterns mimicking real verification scenarios
(`bench-multiplication/realistic-patterns/`):

| Pattern | with pair | detection | without pair | win? |
|---------|----------:|----------|-------------:|-----:|
| `p1_modmul_comm.c` (RSA-style modmul) | T/O@300 s | 1 pair | T/O@300 s | no — modular reduction dominates |
| `p2_crc_chain.c` (FNV-like hash) | T/O | 0 pair | T/O | no — pair detection doesn't fire (XOR-based chain) |
| `p3_pixel_index.c` (image pixel index) | **1.34 s** | 1 pair | T/O | **yes — >45×** |
| `p4_dot_product.c` (3-term scalar product) | **44.82 s** | 3 pairs | T/O | yes — bounded |
| `p5_polynomial.c` (Horner-style polynomial) | T/O | 0 pair | T/O | no — nested mults, BV resolution gap |
| `p6_overflow_pair.c` (overflow check) | 0.04 s | 1 pair | 0.04 s | trivially fast (simplifier) |
| `p7_bitmix_distrib.c` (distributivity through stored sum) | T/O | 0 | T/O | no — distributivity through stored sum not yet handled |
| `p8_buffer_offset.c` (offset associativity) | **1.37 s** | 1 pair | T/O | **yes — >45×** |

Three out of eight realistic patterns are clearly improved (p3, p4, p8).
One is trivially fast (p6, simplifier handles it). Four are not helped
because the bottleneck is something other than multiplier-equality
reasoning (modular reduction, XOR-laundering, distributivity through
stored sum, or nested mults whose intermediate result_bv link is broken
by `store()` in p5).

The wins are precisely the cases the detector targets. The non-wins
are documented limitations and clear future-work targets.

## 10. Where pair detection does not help

Summarising from §6, §7, §9:

| Cause of non-help | Examples | Reason |
|-------------------|----------|--------|
| The multiplier is not the bottleneck | `p1_modmul_comm` (modular reduction) | Equality between multiplications is asserted but the SAT solver still has to reason about `% m`, which is the dominant cost |
| The benchmark has no commuting multiplier | SV-COMP bitvector, auto-large `tree`, etc. | The detector correctly fires zero times and adds no overhead |
| Pair detection's pattern matcher is incomplete | `hash_mul.c` (SSA renaming through inlined function) | Future work: bit-blast caching or expression-level SSA chase |
| Distributivity hidden through opaque sum | `p7_bitmix_distrib.c` | Future work: extend the BV-level resolution to track addition results |
| Algebraic identity not in the catalogue | `(-a)*(-b) == a*b`, `a*a + 2*a*b + b*b == (a+b)^2` | Future work: extend the pattern catalogue |

In all cases, pair detection causes no regression: when it doesn't help
it also doesn't hurt.

## 11. Future work

Ranked by expected payoff per implementation cost:

1. **Distributivity through opaque sum** (modest cost, modest payoff):
   track plus_exprt approximations alongside mult and resolve through
   them. Catches `p7_bitmix_distrib.c` and similar.

2. **Bit-blast caching** (large cost, large payoff): cache bit-blast
   results so `(a >> 16) ^ a` appearing twice produces the same BV.
   This generalises beyond multiplications and would close the
   `hash_mul.c` gap. It is the most architecturally valuable
   extension.

3. **Strip-lemma injection** (already explored, rejected): emitting
   Beame-Liew strip CNF as redundant clauses alongside the equality
   does not help in any case we tested. Documented in
   `doc/beame-liew-refinement.md`.

4. **Pair detection across non-multiplications** (modest cost, broader
   reach): same flat-multiset framework could detect commutative pairs
   of bitwise AND, OR, XOR and additive pairs of additions. Would not
   benefit from algebraic insight beyond what simplifier already
   provides, but adds robustness for inlined-parameter cases.

5. **Public benchmark validation at scale** (no implementation cost):
   try AWS C Common, NASA Apex, Linux kernel snippets through CBMC's
   `integration/` tooling. Best done after a pull-request landed and
   integrated CI is available.

6. **Submit the contribution upstream** (engineering cost): prepare PR
   description and submit to `diffblue/cbmc:develop`.

## 12. File index for reproducibility

Each artifact below is checked in to the `features/adder` branch:

### Code

- `src/solvers/refinement/refine_arithmetic.cpp` — implementation,
  including the experimental `REFINE_MULT_MODE = 4` and
  `detect_algebraic_pairs`.
- `src/solvers/refinement/bv_refinement.h` — declaration.
- `src/solvers/refinement/bv_refinement_loop.cpp` — invocation site.

### Regression tests

- `regression/cbmc-incr-oneloop/multiply-stored-pairs-refine/`
- `regression/cbmc-incr-oneloop/multiply-distributivity-refine/`

### Benchmarks and data

- `bench-multiplication/comparison-study.tsv`
- `bench-multiplication/scaling-pair-detection.tsv`
- `bench-multiplication/scaling-distributivity.tsv`
- `bench-multiplication/sv-comp-results.tsv`
- `bench-multiplication/auto-large-results.tsv`
- `bench-multiplication/realistic-patterns/p1..p8.c`
- `bench-multiplication/realistic-patterns/results.tsv`
- (Existing) `bench-multiplication/{comm,assoc,distrib,widen_mul,mod_mul,
   hash_mul,matrix_mul,matrix_trace_16,mac_equiv,...}.c`

### Scripts

- `bench-multiplication/run-pair-detection-scaling.sh`
- `bench-multiplication/run-distributivity-scaling.sh`

### Documentation

- `doc/beame-liew-refinement.md` — running developer-facing log.
- `doc/pair-detection-paper-writeup.md` — this document.

### Build commands

```
cmake -S . -Bbuild
cmake --build build --target cbmc -j$(nproc)
```

For A/B comparison:

```
# With pair detection (default):
./build/bin/cbmc <benchmark> --refine-arithmetic --no-standard-checks

# Without pair detection:
CBMC_DISABLE_REFINE_PAIR_DETECTION=1 \
  ./build/bin/cbmc <benchmark> --refine-arithmetic --no-standard-checks
```

To regenerate scaling data: `bash bench-multiplication/run-pair-detection-scaling.sh`
or `run-distributivity-scaling.sh` (each takes ~30 minutes at 180 s
timeout per cell).

## Acknowledgments

The N3 Beame-Liew polynomial-proof reproduction (in
`bench-multiplication/n3-beame-liew/`) provided the conceptual scaffold
for this contribution. The technique here uses a substantially simpler
mechanism than the polynomial-proof generator (constant-size equality
assertion versus polynomial-size DRAT certificate), but the underlying
insight that bit-vector multipliers admit polynomial-size proofs of
algebraic identities is shared.

Beame, Paul, and Vincent Liew. "Towards verifying nonlinear integer
arithmetic." Computer Aided Verification (CAV), 2017.
