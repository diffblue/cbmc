# Beame-Liew strips in `--refine-arithmetic`

This document records an attempt to apply Beame & Liew's polynomial-size
proof structure for array-multiplier commutativity (Beame & Liew, 2017)
to CBMC's `--refine-arithmetic` refinement loop, as `REFINE_MULT_MODE = 4`
in `src/solvers/refinement/refine_arithmetic.cpp`.

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
