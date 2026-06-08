# Phase 1 (Plan B) findings: where wide-ring algebraic does vs does
# not pay off

This document records the empirical reconnaissance done to validate
or refute the original Plan B hypothesis (a hybrid Z/ZMod
polynomial system would unlock +5 to +12 SMT-COMP benchmarks via
wide-ring overflow reasoning).

## Negative findings on synthetic benchmarks

I constructed a series of synthetic UNSAT benchmarks of the form
"prove `(extract 2N-1 N) (bvmul (zext s) (zext t)) = 0` given
bvult/bvule bounds on s and t". For Plan B to be useful, bit-
blasting should struggle on these and wide-ring algebraic should
refute them faster.

**Result: bit-blasting solves these patterns very fast on its
own.**

| Bitwidth | Pattern | Bit-blast | Default (algebraic + bit-blast) |
|---|---|---|---|
| 4 | `s, t < 4` | 0.005s | 0.005s |
| 16 | `s, t < 256` | 0.006s | 0.006s |
| 32 | `s, t < 65536` | 0.013s | 0.013s |
| 64 | `s, t < 2^32` | 0.012s | 0.012s |
| 128 | `s, t < 2^32` | 0.119s | 0.119s |
| 256 | `s, t < 10^36` | 0.267s | **60s T/O** |
| 256 | `s, t <= 10^6` | 0.139s | (similar T/O) |
| 64 | `single mul, a,b<=10^9` | 0.021s | **4.73s** |

Two key observations:

1. **Bit-blasting + canonicalisation handles overflow-with-bound
   patterns very efficiently, even at 256 bits.** When the bvult/
   bvule bound is a power of 2, constant propagation through
   the bit-multiplier zeros out high bits trivially. Even with
   non-power-of-2 bounds, the SAT-side propagator is fast.

2. **The current algebraic pipeline regresses (slows down) on
   these patterns.** With `DISABLE_ALGEBRAIC=1`, the 256-bit
   case solves in 0.27s. Without disabling, the same case T/Os
   at 60s — a >220× slowdown. This is a separate engineering
   issue worth fixing on its own (independent of Plan B).

Reproduction:
```
DISABLE_ALGEBRAIC=1 timeout 60 build/bin/smt2_solver \
  < doc/paper-algebraic/data/overflow_synth_256.smt2  # ~0.27s

timeout 60 build/bin/smt2_solver \
  < doc/paper-algebraic/data/overflow_synth_256.smt2  # T/O
```

### Does the synthetic regression affect SMT-COMP?

I ran the full SMT-COMP stratified sample (66 benchmarks) with
default vs `DISABLE_ALGEBRAIC=1`, comparing per-benchmark times:

| Configuration | Solved | Slowdowns (>3× and >5s) |
|---|---|---|
| default (Plan A.1+A.2) | **39/66** | n/a |
| `DISABLE_ALGEBRAIC=1` | 31/66 | n/a |
| Cross-comparison | +8 unlocks for default | **0 benchmarks slowed >3×** |

So the synthetic regression does NOT affect any benchmark in the
sample. The algebraic pipeline contributes +8 unlocks vs purely
bit-blasted, with no observable cost on the remaining 58.

**Implication**: the synthetic-benchmark regression is
theoretical — useful to know about but not impacting our
empirical evaluation. Engineering fix is low priority.

## What this implies for the original Plan B hypothesis

The Plan B design targets ~16 SMT-COMP benchmarks with overflow
or bvudiv slicing patterns. Closer examination:

- **brummayerbiere2_*ulov\* (5)**: overflow-detection circuits.
  The high-half of bvmul is one side of an equivalence assertion;
  the OTHER side is a deeply nested AND/OR/NOT tree on individual
  bits of the inputs. Plan B's wide-ring captures the integer
  side of the equivalence but cannot reason about the bit-level
  Boolean circuit. The benchmark needs gate-level (AIG-aware)
  reasoning of the kind in Biere-Kauers-Ritirc 2017 and
  Kaufmann-Biere 2021 (cited in our paper as
  `biere2017challenges`, `kaufmann2021amulet`). Our paper already
  acknowledges this as a gap (Section "Gate-level equivalence is
  a gap").

- **log-slicing_\* (5)**: bit-level slicing equivalence checks
  (translation of bvudiv to base operations via concat/extract).
  These are pure gate-level circuit equivalence problems with
  no overflow content. Plan B's wide-ring is not applicable.

- **galois_iffyInterleavedModMult (2)**: complex modular
  arithmetic equivalences, primarily bit-level.

- **calypto_problem_16, BuchwaldFried, isqrtadd, Booth_mult (4)**:
  gate-level circuit equivalence problems.

- **brummayerbiere4_unconstrained0\* (5)**: out-of-memory failures
  in bit-blasting — neither Plan B nor Plan A applies.

- **VS3_A11/S1 (2)**: 500+ separate polynomial assertions; the
  problem is the algebraic worklist scaling to many constraints,
  not overflow reasoning.

- **Favaro_mul_mba_synthesis (1)**: mixed Boolean-arithmetic
  identity using bvor/bvxor/bvshl. Needs MBA-aware decomposition,
  not wide-ring.

- **Sage2_bench_9381 (1)**: mixed-bitwidth polynomial constraints,
  unrelated to overflow.

**Plan B's unlocks on the SMT-COMP sample are likely 0–2, not the
projected +5 to +12.** The projection assumed Plan B would handle
the brummayerbiere2_\*ulov\* family; a more careful read of the
benchmarks shows they require gate-level reasoning that Plan B
explicitly does not address.

## What we observe on the polynomial-identity SMT side

By contrast, polynomial identities (like Karatsuba's identity) at
high bitwidth are a clear ALGEBRAIC win:

| Benchmark | Bit-blast | Default (with algebraic) |
|---|---|---|
| Karatsuba, 64-bit | **30s T/O** | **0.068s** (440× faster) |
| `(a*b)*(c*d) = (a*c)*(b*d)`, 512-bit | 0.004s | 0.004s |

The Karatsuba result is a concrete demonstration that polynomial
identities scale better algebraically than via bit-blasting.

## What we observe on the bvudiv side

I found a clear gap on the bvudiv side. The current bvudiv encoding
is `q*t + r - s = 0` (an over-approximation: it does not enforce
`0 <= r < t`). This means the standard div/mod identity
`a == (a/b)*b + (a%b)` is NOT refutable by our algebraic pipeline:

| Benchmark | Bit-blast | Default (with algebraic) |
|---|---|---|
| div/mod identity 32-bit | <1s | **30s T/O** |
| div/mod identity 256-bit | <1s | **60s T/O** |

To unlock div/mod identity, the bvudiv encoding needs the
range constraint `0 <= r < t`. This is **Plan A.3** territory.
It is a smaller and more concrete extension than Plan B's wide-
ring infrastructure.

## Recommendation

1. **Skip large-scale Plan B implementation.** The projected
   unlocks aren't real for our sample. The wide-ring architecture
   is a clean idea but the benchmarks where it would help require
   gate-level reasoning we don't have.

2. **Note the regression**: when the algebraic pipeline encounters
   a high-half-of-zext-product pattern, it should either decline
   (fall through to bit-blasting cleanly) or handle it. Currently
   it spends time without making progress. Worth fixing as
   engineering polish.

3. **Pursue Plan A.3 (bvudiv tightening)**: this addresses a
   concrete, demonstrated gap with a smaller scope. The expected
   unlock count is also +2-4 (small but concrete), and the
   technique is straightforward to formalise.

The honest scientific contribution from Phase 1 is the negative
finding: **modern bit-blasting handles bounded-overflow patterns
efficiently, narrowing the practical scope of pure-overflow
algebraic reasoning to cases where the formula has additional
structure (like a polynomial identity) that bit-blasting cannot
canonicalise.** This refines our paper's positioning of the
algebraic pre-solver as a complement to (not replacement for) bit-
blasting.
