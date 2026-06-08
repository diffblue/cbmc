# Plans A and B — comparison and recommendation

This document synthesises the two detailed plans
(`plan-A-buchberger-tuning.md` and `plan-B-hybrid-z-zmod.md`)
with a comparison table and a recommendation on sequencing.

## Empirical state of the work (post Phase 2.6)

- **SMT-COMP stratified sample**: 36/66 solved.
- **bw=512 family**: 4/5 solving (1, 7, 12, 15; 14 T/O).
- **wienand commute*/distrib***: all 4 solving in ~6ms each.
- **30 unsolved benchmarks** in the SMT-COMP sample, classified:
  - ~12 polynomial-leaning (cohencu*4, geo3.c_5, Sage2_1351 /
    1621 / 9381, Favaro_mul_mba, VS3_*2, brummayerbiere4_unconstrained*5,
    ultimate_s3_srvr): require Plan A.
  - ~16 bit-level / circuit-equivalence (brummayerbiere2_*ulov *5,
    log-slicing_bv*div_*5, galois_*ModMult *2, BuchwaldFried,
    isqrtadd, Booth_mult, calypto): require Plan B.
  - ~2 mixed / unclear.

## Comparison table

| Aspect                     | Plan A: Buchberger tuning + walk    | Plan B: Hybrid Z/ZMod          |
|----------------------------|-------------------------------------|--------------------------------|
| **Effort**                 | ~2 weeks                            | ~3-4 weeks                     |
| **Lines of code**          | ~250                                | ~1200                          |
| **Risk**                   | Low to medium                       | Medium to high                 |
| **Architectural impact**   | Minimal (extends existing pipeline) | Major (new wide-ring system)   |
| **Soundness story**        | Existing (no change)                | New bridging theorem needed    |
| **Empirical evidence base**| Strong (cohencu_simple unlocks confirmed at bw=8/16/32)| Speculative (Phase 2.7 attempts hit architectural walls; Plan B is the unblocking design) |
| **Expected unlocks**       | +5 to +8                            | +5 to +12                      |
| **Target benchmark cluster**| Polynomial-fragment (cohencu, geo3, Sage2_*, Favaro)|Bit-level overflow (brummayerbiere2_ulov*, log-slicing*, galois*) |
| **Lean formalisation**     | ~100 lines (~2 new theorems)        | ~200 lines (new HybridRing module) |
| **Paper-novelty**          | Strong (LIFO→normal selection finding is a publishable empirical result) | Strong (hybrid Z/ZMod design is a novel architectural contribution) |
| **Ablation possibility**   | High (env var DISABLE_*)            | High (env var, runs only on overflow patterns) |

## Sequencing recommendation

**Do Plan A first, Plan B second.**

Reasons:

1. **Plan A is lower risk and faster**. Plan A's core finding
   (LIFO → normal pair selection) is empirically validated and
   produces zero regressions. Plan B requires careful new design.

2. **Plan A's walk infrastructure is reusable**. The bounded
   tree-walk of Phase 2.7's revised attempt is needed by Plan A
   for cohencu_*. Plan B doesn't strictly need it, but the
   infrastructure is generally useful.

3. **Each plan targets a distinct cluster**. Doing them in either
   order doesn't change total unlock count. But Plan A's faster
   completion means earlier paper updates and a stronger initial
   contribution.

4. **The empirical evidence for Plan A is concrete; for Plan B
   it's projected**. Plan A: cohencu refutes in 9 steps with
   normal selection (proven on synthetic test). Plan B: would
   unlock log-slicing / brummayerbiere2 IF the wide-ring
   reasoning fires correctly (requires implementation to verify).

5. **Plan A keeps the architecture simple**. If Plan A delivers
   the expected +5 to +8 unlocks, that may be sufficient for the
   paper. Plan B can be a separate follow-up paper or a deferred
   extension.

## Combined timeline

If we do both plans sequentially:

- **Week 1-2**: Plan A (Buchberger tuning + walk).
  - Day 1: A.1 pair selection. Run benchmarks. Confirm 0
    regressions.
  - Days 2-4: A.2 walk + IF-rebuild with proper gating. Iterate
    on regression patterns.
  - Days 5-6: Lean formalisation (StrongGB.lean updates +
    AlgebraicTreeWalk.lean).
  - Days 7-10: Test suite, paper updates, regression checks.
- **Week 3**: review and stabilise Plan A. Commit.
- **Weeks 4-6**: Plan B (Hybrid Z/ZMod).
  - Week 4: hybrid extractor architecture, overflow pattern
    recognition.
  - Week 5: bit-decomposition coordination, wide-system
    integration in `try_algebraic_solve`.
  - Week 6: Lean formalisation (HybridRing.lean), benchmark
    validation, paper updates.

**Total**: ~6 weeks. Final SMT-COMP coverage estimate: 36/66 →
46-56/66 (depending on how many of the projected unlocks
materialise).

## What if we only have time for one?

If we MUST pick one, **Plan A**:

- Higher confidence (empirical evidence already strong).
- Faster (2 weeks vs 4 weeks).
- Lower risk (preserves existing architecture).
- The pair-selection finding is publishable on its own as a
  "small-but-important" contribution.

Plan B can be deferred to a follow-up paper.

## What if Plan A turns out empirically less promising than projected?

The +5 to +8 unlock estimate for Plan A is based on:
- 4 cohencu unlocks (high confidence; verified in synthetic form
  at bw=4-32).
- 1 geo3.c_5 unlock (verified in walk + GB experiment).
- 0-3 additional from polynomial-leaning benchmarks (Favaro,
  Sage2_*, VS3_*, Ultimate_s3) — speculative based on
  bvmul-presence + arithmetic-only structure.

If the actual unlock count is lower (e.g., only 2 cohencu unlocks
because cohencu_2 / cohencu_3 differ), the floor is +1 to +2
unlocks. Even at the floor, the pair-selection finding is a
worthwhile commit (zero-regression infrastructure improvement
that may help future benchmarks).

## Decision points

User input needed before proceeding:

1. **Do Plan A first?** If yes, we start with A.1 (pair selection).
2. **Do both plans in sequence?** If yes, ~6 weeks.
3. **Stop here, write up Phase 2.5 + 2.6?** Acknowledge plans as
   future work.

My recommendation is **(1) Do Plan A first**, then assess based
on actual unlocks whether to proceed with Plan B.
