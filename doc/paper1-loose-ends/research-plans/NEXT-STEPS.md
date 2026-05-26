# Next Steps (Paper 1 and Paper 2)

Snapshot updated 2026-05-12 after Phase 3 Cut(row)-merging.

## Status

### Research plans
| # | Plan | Status |
|---|---|---|
| N1 | Characterising the CDCL-vs-Beame-Liew gap | **Open** (never executed) |
| N2 | Controlled experiment isolating carry propagation | **Done** -- in Paper 1 Section 3 |
| N3 | Implementing Beame-Liew's critical-strip construction | **Advanced** (see below) |
| N4 | Multi-encoding ablation | **Done** -- Paper 1 Appendix |

### N3 progress detail (2026-05-12 follow-up session)
- Phase 1 (flat case-analysis DRAT): **DONE**, validates, 4-10x
  smaller than CaDiCaL raw, 2.5-4x smaller than CaDiCaL trimmed
  core at n>=5.
- Phase 2 structural (per-column DRAT): **DONE**, validates, 2n
  times larger than Phase 1.
- Phase 3 step 1 (strip extraction): **DONE**, Lemma 3.1 UNSAT
  verified.
- Phase 3 step 2 (BP construction + DRAT translation):
  **DONE** (v9 paper-order BP, and cut_v2 Cut(row)-merging BP).
  Both validate with drat-trim.
- Phase 3 full proof composition: **DONE**, validated at n=3..6
  via `phase3_full.py` (v9) and `phase3_full_cut.py` (cut_v2).
  cut_v2 reduces per-strip DRAT by 3-5x at n=3..5.
- Phase 3 polynomial O(n^6 log n) scaling: **PARTIAL**. BP is
  polynomial-in-k for small k (k=3: 116 nodes regardless of n)
  but still exponential-ish for middle k due to ripple-carry's
  wider state per row. Paper's bound assumes CSA tableau.

### Remaining work for true polynomial (for future session)
1. Switch from ripple-carry to CSA tableau multiplier (matches
   paper's model; Cut(j) becomes O(log n) bits).
2. Alternative: use RAT extension variables to encode BP DAG
   structure directly, avoiding the tree-unfolding that defeats
   merging in the current approach.
3. Measure for n=7, 8 with sufficient memory; extrapolate scaling.
  2. Branch on incoming carry boundary at col k-Delta-1.
  3. Branch on tableau row-by-row.
  4. Merge on Cut(j) of size O(log k).
  5. Translate DAG BP to DRAT via Krajicek Prop. 2.1.
  Estimated effort: 2-3 more focused sessions.

### Papers
- **Paper 1 (bitblasting)**: 21 pages, body ends page 15, two
  senior-review passes applied, Wallace + Burch + Kumar + Dutertre
  cited. Phase 1/2 results could be folded in as a one-sentence §8
  or §9 addition if desired.
  - Blockers: target venue not pinned; template (ceurart.cls) is
    CEUR-specific; two intros diverge between repos.
- **Paper 2 (algebraic)**: 20 pages. Has NOT had its own
  senior-review pass in this session. TACAS 2027 deadline: 15 Oct
  2026.

### Items flagged as "future work" in text
- Full-suite QF_BV evaluation (Section 7.9) -- approximately
  16,000 benchmarks.
- Automating the proof-guided loop (Section 10).
- Extending encoding selection to deeper structural properties
  (Section 10).
- Reconciling encoding-level with solver-level and inprocessing-
  level guidance (Section 10).

## Recommended order

### Submission-critical (needs decisions from user)
1. Pin Paper 1's target venue.
2. Decide on template (SAT/FMCAD/CAV use LNCS; CEUR uses
   ceurart).
3. Reconcile the two Paper 1 intros (multiplier-encodings.git is
   canonical).
4. Push Paper 1 commits to tautschnig/multiplier-encodings.

### High-value, moderate effort
5. **Senior-review pass on Paper 2.** Same treatment as Paper 1.
   TACAS deadline is 15 Oct 2026.
6. **Fold Phase 1 N3 result into Paper 1** as a one-sentence
   addition to Section 8 or 9 (validates "structure matters"
   thesis with an independent proof comparison).
7. **N1 Approach A -- empirical characterisation of the gap.**
   Effort: ~1-2 weeks compute + writeup.

### Speculative / larger scope
8. **Complete N3 Phase 3** (polynomial BP construction). Estimated
   2-3 focused sessions on top of current scaffolding. Documented
   concretely in options-B-A.md.
9. **Full-suite SMT-COMP QF_BV run.** Expensive, likely same
   qualitative answer.
10. **Automate the proof-guided loop.** Separate paper.

## Concrete recommendation snapshot

- Today/this week: resolve submission mechanics for Paper 1
  (steps 1-4).
- Next 1-2 weeks: senior-review pass on Paper 2 (step 5).
- In parallel (low-priority): fold N3 Phase 1 result into Paper 1
  (step 6), or continue N3 Phase 3 in focused sessions (step 8).

(Update this file when priorities shift.)
