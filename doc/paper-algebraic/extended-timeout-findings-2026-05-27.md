# Extended-timeout SABER experiments and GRS framing (2026-05-27)

This document records the empirical answers to two questions:

1. **What does the GRS benchmark set actually demonstrate for Paper 2?**
2. **Can a 30-minute timeout unlock SABER results that 60-second
   timeouts cannot?**

## Q1: GRS benchmark relevance to Paper 2

**Empirical setup:** The 20 GRS benchmarks (`20230224-grsbits-truby`)
verify floating-point multiplication via word-level shift-add
patterns. They contain `bvshl`, `bvlshr`, `bvadd`, `bvsub`, `bvuge`
operators — and notably **no `bvmul`**.

**What GRS does NOT demonstrate for Paper 2:**

- **The algebraic Gröbner-basis layer never fires.** Verified
  empirically: running grs-128-16 with `DISABLE_ALGEBRAIC=1`
  (pure bit-blasting) takes 37.05 s; with the algebraic layer
  enabled, 37.46 s. Within ±2 % — the algebraic layer adds no
  value because there's no `bvmul` for it to find polynomial
  structure in.
- **Re 4 (bit-decomposition for `bvlshr`/`bvashr`/bitwise) is
  inert.** Without `bvmul`, even the bit-decomposed shift cannot
  combine into a useful polynomial relation.
- **The improvement from 3/20 to 7/20 between 30 s and 60 s
  timeout is not a Paper 2 result.** It's about CBMC's
  bit-blasting backend solving more given more time; Bitwuzla
  improves the same way (5/20 → 6/20).

**What GRS marginally does demonstrate:**

- **No regression.** Our SMT solver (with the algebraic layer
  enabled) is competitive with Bitwuzla on bit-blasting-friendly
  benchmarks. The algebraic layer is correctly silent when it
  can't help.
- **One unique 60 s solve** (grs-96-32, where Bitwuzla times out
  at 60 s but we solve in 56 s). At 120 s Bitwuzla also gets it.

**Recommendation for Paper 2's §4.6:**

GRS belongs in §4.6 only as a transparency / scope-check, not as
a flagship empirical result. Two acceptable options:

1. **Drop §4.6 entirely.** Paper 2's empirical centrepiece is
   the random-polynomial / DSP benchmark suite, where the
   algebraic layer wins. GRS distracts from this.
2. **Strip §4.6 to one paragraph.** "On benchmarks without
   `bvmul`, our algebraic layer is silent and we match the
   bit-blasting baseline (CBMC 7, Bitwuzla 6, cvc5 1 at 60 s
   on 20 GRS benchmarks)."

Either is more honest than presenting GRS as a Paper 2 win.

## Q2: 30-minute timeout for SABER

We ran two classes of extended-timeout experiments:

### (i) SABER karatsuba2 scaling beyond N=256

The §4.3 headline result is "schoolbook = 2-level Karatsuba SABER"
verified up to N=256 in ~109 s. Question: does extending to 30 min
let us go further?

**Result: no — but for a different reason.** SABER karatsuba2 hits
a **memory wall**, not a time wall, between N=256 and N=320:

| N | Peak RSS | Status (with ulimit 57 GB, 30 min) |
|---|---|---|
| 256 | 29 GB | unsat in 109 s ✓ |
| 320 | >29 GB | std::bad\_alloc at 82 s |
| 384 | >29 GB | std::bad\_alloc at 82 s |
| 512 | >57 GB | std::bad\_alloc at 160 s |
| 1024 | >57 GB | std::bad\_alloc at 0 s |

The memory growth is in the polynomial extraction step
(`poly_extract.cpp::to_polynomial`), not in Buchberger. Increasing
the timeout doesn't help because the procedure crashes before
finishing extraction.

**Implication:** The §4.3 "scales to SABER's actual N=256" claim
is the structural ceiling of our current implementation. Going to
N=512 (or larger) requires reducing the polynomial extraction's
memory footprint, not extending the timeout. This is a separate
follow-on (memory-efficient extraction; perhaps streaming
polynomials, perhaps a different polynomial representation).

### (ii) Faithful Toom-Cook 4-way SABER at 30 min

Sub-goal 4 (commits `e98a21b043` etc.) identified faithful
Toom-Cook 4-way SABER as an open challenge; bitwuzla, cvc5, and
our procedure all time out at 60-180 s on N=4 single-coefficient
queries. Question: does 30 min suffice?

**Result: no.** All runs timed out at 1800 s:

| Query | Solver | 60 s / 180 s | 30 min (1800 s) |
|---|---|---|---|
| Toom-4 N=4, all coeffs, q-mod | bitwuzla | T/O | **T/O** |
| Toom-4 N=4, c[0] only, q-mod | bitwuzla | T/O | **T/O** |
| Toom-4 N=4, c[0] only, q-mod | smt2_solver | T/O | **T/O** |

**Implication:** The intractability is genuine, not a near-miss.
SABER's faithful Toom-Cook 4-way is beyond current SMT capability
at any feasible budget. The "open challenge" framing in the §4.3
recommendation (and `toom-cook-4way-finding-2026-05-27.md`) holds.

## Summary

- **GRS** doesn't demonstrate Paper 2's contribution. The recent
  improvement (3/20 → 7/20) is timeout-related, not Re 4-related.
  Recommend dropping or stripping §4.6.
- **SABER karatsuba2 extended scaling** is memory-bound, not
  time-bound. Extended timeout doesn't help. Memory-efficient
  extraction is a separate follow-on.
- **SABER faithful Toom-Cook 4-way** is intractable at 30 min for
  all tested SMT solvers, confirming the "open challenge" framing.

## Cross-references

- `grs-results-2026-05-27.md` — full GRS measurement data.
- `saber/toom-cook-4way-finding-2026-05-27.md` — Toom-Cook 4-way
  generator and intractability finding (now updated with 30-min
  results).
- `re4-bit-decomposition-design-2026-05-27.md` — Re 4 design.
- `future-directions-2026-05-27.md` — master tracker.
