# Next Steps (Paper 1 and Paper 2)

Snapshot updated 2026-05-12 after Phase 3 BP-DRAT breakthrough.

## Status

### Research plans
| # | Plan | Status |
|---|---|---|
| N1 | Characterising the CDCL-vs-Beame-Liew gap | **Open** (never executed) |
| N2 | Controlled experiment isolating carry propagation | **Done** -- in Paper 1 Section 3 |
| N3 | Implementing Beame-Liew's critical-strip construction | **Partial** (see below) |
| N4 | Multi-encoding ablation | **Done** -- Paper 1 Appendix |

### N3 progress detail (2026-05-12 session)
- Phase 1 (flat case-analysis DRAT): **DONE**, validates, 4-10x
  smaller than CaDiCaL raw, 2.5-4x smaller than CaDiCaL trimmed
  core at n>=5.
- Phase 2 structural (per-column DRAT): **DONE**, validates, 2n
  times larger than Phase 1.
- Phase 3 step 1 (strip extraction): **DONE**, Lemma 3.1 UNSAT
  verified.
- Phase 3 step 2 (BP construction + DRAT translation):
  **DONE** (first validation). `phase3_bp_drat_v9.py` emits
  per-strip DRAT that validates with drat-trim via Prop 2.1
  post-order resolution on a tree-unfolded BP.
  `phase3_full.py` composes all strip DRATs into a full
  commutativity proof (validated at n=3..6).
- Phase 3 polynomial O(n^6 log n) scaling: **OPEN**. The
  current BP merges on UP-state, not the paper's Cut(j) state,
  yielding exponential (not polynomial) size in k. Making the
  BP use the paper's Cut(j) state signature is concrete future
  work documented in `options-B-A.md`.
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
