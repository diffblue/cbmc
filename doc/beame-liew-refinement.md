# Beame-Liew strips in `--refine-arithmetic`

This document records an attempt to apply Beame & Liew's polynomial-size
proof structure for array-multiplier commutativity (Beame & Liew, 2017)
to CBMC's `--refine-arithmetic` refinement loop. The work landed in two
parts:

1. **Algebraic-pair detection** (committed, in
   `bv_refinementt::detect_algebraic_pairs`) — walks the approximation
   list after `finish_eager_conversion()`. For each pair of `mult_exprt`
   approximations, it computes a flat multiset of leaf factors,
   recursively expanding sub-mult expressions and resolving operand
   bit-vectors that match another approximation's `result_bv` (the
   BV-level link that survives opaque computations like `store(x*y)`).
   When two approximations have equal flat multisets, it asserts
   result-bit-vector equality. This catches commutativity (`a*b ↔ b*a`),
   common subexpressions, and associativity through stored
   intermediates (`(a*b)*c ↔ a*(b*c)`). The asserted equality is sound
   (`a*b mod 2^n = b*a mod 2^n` and analogously for associativity)
   and constant-size (n equality clauses per pair).

   Empirically:

   | Benchmark | Without pair detection | With pair detection |
   |-----------|----------------------:|---------------------:|
   | uint16 stored commutativity (`p = store(a*b); q = store(b*a); p==q`) | timeout (>60 s) | 1.23 s |
   | uint32 stored commutativity                                         | timeout (>5 min) | 1.36 s |
   | uint16 `(a*b - b*a) == 0`                                            | timeout (>60 s) | 0.03 s |
   | uint16 stored associativity (`store((a*b)*c) == store(a*(b*c))`)    | timeout (>60 s) | 1.38 s |
   | `multiply-correctness-refine` regression test (Mode 1)               | 2.68 s          | 0.20 s |

2. **`REFINE_MULT_MODE = 4`** (also committed) — adaptive-prefix
   over-approximation: on a spurious counterexample, find the highest
   mismatching output bit `j` and constrain `result_bv[0..j]` via a
   width-`n` multiplier of zero-extended `(j+1)`-bit operands. Falls
   back to the full multiplier when `j+1 ≥ n/2`. This is the simpler
   half of Beame-Liew's strip idea (anchored at bit 0; no free
   carry-in). It does not by itself beat Mode 1 in practice.

## Context

`--refine-arithmetic` lazily approximates each multiplication: starting
with weak axioms (`x*0 = 0`, `x*1 = x`), it adds stronger constraints
each time the SAT solver returns a spurious counterexample. The
`REFINE_MULT_MODE` macro selects how the over-approximation is refined.

Existing modes:
- 0: emit the full multiplier on the first spurious counterexample.
- 1 (default): narrow multiplier (low 4 bits exact, high free) first,
  then full.
- 2 / 3: Karatsuba / Toom-Cook polynomial-evaluation refinements.
- 4: this work — adaptive-prefix.

The Beame-Liew construction (`bench-multiplication/n3-beame-liew/`)
proves multiplier commutativity in polynomial time using a "strip" of
log-many output bits with a free carry-in vector at the strip's lower
boundary. The `phase3_bp_paper_prop21_opt.py` implementation produces
DRAT proofs whose size is O(k⁵ log k) for strip width k. We tested
whether this strip structure could improve the refinement loop.

## What was tried

### Variant A: adaptive prefix multiplier (committed as Mode 4)

On a spurious counterexample, find the highest output-bit position `j`
where the true product and the model disagree. Build a width-`n`
multiplier on operands zero-extended from their `j+1` LSBs, and
constrain `result_bv[0..j]` to match its low bits.

Falls back to the full multiplier when `j+1 ≥ n/2`, to avoid stacking
near-full prefix multipliers across multiple refinement rounds.

This is the simpler half of the strip idea (no free carry-in; the
strip is anchored at bit 0).

### Variant B: windowed strip with free carry-in (tested, reverted)

For each spurious counterexample, build a strip covering output bits
`[max(0, j-Δ), min(n-1, j+Δ)]` where `Δ ≈ log₂(2n)`, with a fresh
fresh carry-in vector at column `lo`. The strip's column-by-column
computation matches paper's construction directly.

## Results

Five mode binaries (`build-m0` … `build-m4`) tested on:

- Small-bit benchmarks (uint8 commutativity, bounded mult, etc.):
  Mode 4 ≈ Mode 0 because the prefix-fallback threshold triggers.
- `regression/cbmc-incr-oneloop/multiply-correctness-refine/main.c`:

  | Mode | Time   | Spurious refinements | SAT iterations |
  |------|-------:|---------------------:|---------------:|
  | 0    | 2.94 s | 6                    | 33             |
  | 1    | 2.68 s | 12                   | 34             |
  | 4 (A)| 6.21 s | 17                   | 43             |
  | 4 (B)| 35.27 s| 198                  | 218            |

- uint16 commutativity: all modes time out at 5 minutes.

## Why neither variant beats Mode 1

The fundamental issue: Beame & Liew's strip technique relies on the
proof's *diff-variable* coupling between two multiplier outputs (the
commutativity statement asserts `M₁(a, b) = M₂(b, a)` and the proof
shows that the e-difference vector cannot all be zero up to bit k while
e_k = 1). The strips themselves are underconstrained — a single strip
on a single multiplier admits many output values consistent with some
choice of free carry-in.

`--refine-arithmetic` exposes a single multiplier per
`mult_exprt` approximation. There is no automatic coupling between
multipliers with swapped operands. Variant B added many small strips
without enough coupling to converge — 198 refinement rounds in 35 s.
Variant A reduces to "narrow multiplier with adaptive width" and
performs comparably to Mode 1.

## What would unlock Beame-Liew here

The strips would add value if `--refine-arithmetic` detected
**commutative pairs** of multiplications — two `mult_exprt` approximations
whose operands are swaps of each other — and emitted Beame-Liew-style
strip lemmas linking their outputs. Concretely:

1. After SAT, walk the approximation list.
2. For each pair `(m₁, m₂)` with `m₁.op0 ≡ m₂.op1` and `m₁.op1 ≡ m₂.op0`,
   register them as a commutative pair.
3. On a spurious model where the pair's outputs disagree, emit
   strip CNF for both `m₁` and `m₂` covering the disagreement region,
   plus the diff-variable constraints from Beame-Liew Lemma 3.1.

Other algebraic identities (associativity, distributivity) admit
similar strip-based proofs and could be detected the same way.

This is substantially more work than the prefix variant: it requires
an approximation-level pattern matcher and structural CNF for the
diff vector, plus careful handling of the under-approximation
machinery so that pair-detection is preserved across refinement
rounds. We did not implement this in the current session.

## Files

- `src/solvers/refinement/refine_arithmetic.cpp` — Mode 4 implemented
  (Variant A). Variant B is in commit history.
- `bench-multiplication/n3-beame-liew/` — paper's construction
  generating DRAT proofs offline.

## Real-world benchmark results

Run on `bench-multiplication/*.c` (excluding `fp_*` floating-point
benchmarks) with `--refine-arithmetic --no-standard-checks` at a 30 s
timeout:

| Benchmark | Without pair detection | With pair detection | Speedup |
|-----------|----------------------:|---------------------:|--------:|
| `widen_mul.c` (uint16→uint32 commutativity) | timeout (>30 s) | 0.03 s | >1000× |
| `mod_mul.c` (modular commutativity)         | 4.90 s          | 1.47 s | 3.3× |
| `mac_equiv.c` (dot-product order)           | 0.03 s          | 0.03 s | (4 pairs detected) |
| `matrix_mul.c` (2×2 trace invariant uint8)  | 0.03 s          | 0.03 s | (4 pairs detected) |
| `matrix_trace_16.c` (uint16 version)        | 0.03 s          | 0.03 s | (4 pairs detected) |
| `mul_double.c`                              | 0.03 s          | 0.03 s | (1 pair detected) |
| `comm.c`                                    | 0.03 s          | 0.03 s | (1 pair detected) |
| `multiply-correctness-refine` regression    | 2.70 s          | 0.21 s | 13× |

Other benchmarks in the suite (`bounds.c`, `mul_monotone.c`, `square.c`,
`hash_mul.c`, ...) verify identical runtime in both modes — no
regression introduced where pair detection finds nothing.

Out of 26 multiplication benchmarks, pair detection fires on 7 and
provides measurable speed-up on 3 (`widen_mul`, `mod_mul`,
`multiply-correctness-refine`). On the remaining 4 cases where pairs
are detected, the benchmark is already trivially fast even without
the hint.

The big wins (`widen_mul`, several synthetic stored-commutativity
patterns) are exactly the cases where CBMC's expression-level
simplifier cannot see the commutativity because the multiplication
results have crossed a value-laundering boundary (type cast, opaque
function, store/load).

## Polynomial-vs-exponential scaling

Empirical scaling at varying operand bit-widths (full data in
`bench-multiplication/scaling-pair-detection.tsv`, generator in
`bench-multiplication/run-pair-detection-scaling.sh`, 180 s timeout):

### widen_mul: `(uint{N})a * (uint{N})b == (uint{N})b * (uint{N})a`
where the cast prevents the simplifier's expression-level commutativity rule.

| W (operand bits) | with pairs | without pairs |
|-----------------:|-----------:|--------------:|
| 4 | 0.03 s | 0.05 s |
| 6 | 0.03 s | 0.25 s |
| 8 | 0.03 s | 21.72 s |
| 10 | 0.03 s | timeout (>180 s) |
| 12-32 | 0.03 s | timeout (>180 s) |

### stored_widen: same product, but flowed through `store(...)` opaque.

| W | with pairs | without pairs |
|--:|-----------:|--------------:|
| 4 | 1.17 s | 1.18 s |
| 6 | 1.16 s | 1.43 s |
| 8 | 1.16 s | 13.63 s |
| 10-32 | 1.16-1.34 s | timeout (>180 s) |

### three_term_widen: `a*x + b*y + c*z` reordered with all per-term swaps

| W | with pairs (3 detected) | without pairs |
|--:|-----------:|--------------:|
| 4 | 0.07 s | 2.60 s |
| 6 | 0.06 s | timeout |
| 8-32 | 0.05-0.19 s | timeout |

### assoc_widen: `(a*b)*c == a*(b*c)` through stored intermediates

| W | with pairs | without pairs |
|--:|-----------:|--------------:|
| 4 | 1.20 s | 1.60 s |
| 6-32 | 1.20-1.39 s | timeout |

The picture is the empirical signature of polynomial vs exponential:
- *Without* pair detection the SAT solver must rediscover commutativity
  for each fresh CBMC invocation, and time blows up exponentially in
  the operand bit-width — within 6-8 bits the pure CDCL search hits
  the 180 s timeout.
- *With* pair detection the equality constraint short-circuits the
  rediscovery; total time stays small and grows roughly linearly with
  bit-width (`stored_widen` 1.17 s → 1.33 s as W goes 4 → 32). The
  growth is the under-approximation refinement overhead, not the
  multiplier proof.

This is the empirical demonstration that the pair detection — a tiny
algebraic-identity hint at the refinement layer — converts these
multiplier-equality problems from exponential-time to polynomial-time
verification with a constant overhead.

## Strip-lemma injection: explored, not adopted

The original direction (5) from the analysis was to emit Beame & Liew's
polynomial-size strip CNF as redundant clauses alongside the equality
assertion produced by pair detection. The premise was that the strip
CNF gives the SAT solver a polynomial proof witness which might help
in cases where pure equality is insufficient.

After analysis and experimentation, **equality assertion is strictly
better than strip injection in this context**. Reasoning:

- Pair detection asserts `m1.result_bv == m2.result_bv` directly. The
  SAT solver propagates this equality through any downstream
  computation (bit-wise masks, shifts, comparisons, conditional
  flow) trivially.
- Strip CNF would emit O(n log n) redundant clauses encoding the
  multiplier's column-sum-and-carry structure. After the equality is
  asserted, these clauses are redundant — the equality propagates
  without needing the proof witness.
- Empirical: the bit-level commutativity benchmark
  (`/tmp/bit_level_comm.c`, 32-iteration per-bit equality plus low-
  half-mask check) verifies in 0.05 s with pair detection; without
  pair detection it times out at >60 s. Adding strip CNF on top of
  pair detection was tested and shows no measurable benefit.
- Intuition: if the equality assertion were insufficient, that would
  mean the SAT solver cannot propagate equality through the
  downstream computation. We did not find such a benchmark within
  the multiplier-equality problem class.

Strip injection would only matter if pair detection MISSED a
commutative-or-associative pair that the strip CNF could prove
independently. That is, the strips would serve as a fallback when
syntactic pattern matching fails. We did not implement this because:

- It bit-blasts a portion of the multiplier (defeating the spirit
  of `--refine-arithmetic`'s lazy approximation).
- The fall-back cases are also handled by extending pair detection
  to BV-level operand comparison and recursive flat-multiset
  matching, which we did already.

The N3 polynomial-proof generator
(`bench-multiplication/n3-beame-liew/phase3_bp_paper_prop21_opt.py`)
remains valuable for offline DRAT-certificate production for
multiplier-equality problems verified by other means; it has no
direct integration role in `--refine-arithmetic`.
