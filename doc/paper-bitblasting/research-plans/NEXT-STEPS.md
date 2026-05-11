# Next Steps (Paper 1 and Paper 2)

Snapshot taken 2026-05-11 after the senior-review passes on Paper 1
and the Wallace integration.

## Status

### Research plans
| # | Plan | Status |
|---|---|---|
| N1 | Characterising the CDCL-vs-Beame-Liew gap | **Open** (plan rewritten after Beame-Liew 2019 refutation; never executed) |
| N2 | Controlled experiment isolating carry propagation | **Done** -- in Paper 1 Section 3 |
| N3 | Implementing Beame-Liew's critical-strip construction | **Open** (plan written; never executed) |
| N4 | Multi-encoding ablation | **Done** -- Paper 1 Appendix |

### Papers
- **Paper 1 (bitblasting)**: 21 pages, body ends page 15, two senior-review passes applied, three late citations integrated (Burch 1991, Kumar et al. 2023, Dutertre 2020).
  - Blockers: target venue not pinned; template (ceurart.cls) is CEUR-specific; two intros diverge between repos (multiplier-encodings.git has Martin's rewrite; cbmc-github.git has the older intro).
  - Not pushed to remote.
- **Paper 2 (algebraic)**: 20 pages, builds clean. Has not had its own senior-review pass in this session. TACAS 2027 deadline: 15 Oct 2026.

### Items the paper flags as "future work" (in text)
- Full-suite QF_BV evaluation (Section 7.9) -- approximately 16,000 benchmarks
- Automating the proof-guided loop (Section 10)
- Extending encoding selection to deeper structural properties (Section 10)
- Reconciling encoding-level with solver-level and inprocessing-level guidance (Section 10)

## Recommended order

### Submission-critical (needs a decision)

1. **Pin Paper 1's target venue.**
   - Decide on template (SAT/FMCAD/CAV use LNCS; CEUR uses ceurart; current template only fits CEUR).
   - Reconcile the two intros. The canonical co-authoring repo is
     multiplier-encodings.git, so the default is to adopt its intro
     as the shared one.
   - Push Paper 1 commits to tautschnig/multiplier-encodings once
     happy with state. Nothing is pushed yet.

### High-value, moderate effort

2. **Senior-review pass on Paper 2.** Same treatment as Paper 1
   (front-to-back reviewer read, identify major/moderate/minor issues,
   cuts and moves). TACAS deadline is 15 Oct 2026.

3. **N1 Approach A -- empirical characterisation of the gap.** Run
   shift-add through structural transformations (re-Tseitin, gate
   sharing, congruence elimination, adder topology swaps), measure
   how far each gets CDCL toward the polynomial-size proof Beame-Liew
   guarantee. Could be folded into Paper 1 Section 5 or a new
   subsection. Effort: ~1--2 weeks compute + writeup. Low risk;
   publishable either way.

### Speculative / larger scope

4. **N3 Beame-Liew critical-strip implementation.** Five phases in
   the N3 plan (~6--12 weeks). Phase 1 alone (implement the branching
   program for a single critical strip) is 2--3 weeks. Probably its
   own paper, not a Paper 1 addendum.

5. **Full-suite SMT-COMP QF_BV run.** Expensive (~days of compute).
   Would strengthen Section 7.9's external-validity claim but likely
   give the same qualitative answer ("encoding alone is nearly
   neutral on community sample"). Low scientific upside vs effort.

6. **Automate the proof-guided loop.** Major undertaking; likely a
   separate paper on AI-assisted encoding discovery.

## Concrete recommendation snapshot

- Today/this week: resolve submission mechanics for Paper 1.
- Next 1--2 weeks: senior-review pass on Paper 2.
- In parallel (low-priority): start N1 Approach A.

(This file is meant to be updated when priorities shift.)
