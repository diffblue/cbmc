# Paper 1 (bit-blasting) — Loose Ends Tracker

*Created 2026-05-26.*

Paper 1 ("Proof-Guided SAT Encoding Selection for Multiplication in
Bounded Model Checking") was submitted to **Pragmatics of SAT (PoS)
2026** on 2026-05-11. Peer-review feedback is expected by approximately
2026-06-02.

This directory tracks all open items related to Paper 1 that did not
make it into the submitted version, plus post-submission discoveries
that may inform a future revision.

## Authoritative copy

The submitted version of Paper 1 lives in
`~/multiplier-encodings.git/paper-bitblasting/`. **That is the
authoritative copy.** Until peer review feedback arrives, no
substantive changes should be made to `paper.tex` in either
location: changes might confuse the authors' tracking of what was
submitted vs.\ post-submission revision.

This `doc/paper1-loose-ends/` directory in `cbmc-github.git`
collects:

- Research-direction documents that discuss work for the *next*
  iteration of Paper 1 (post peer review) or for follow-up papers.
- Bug-investigation reports for issues discovered after submission.
- Experimental data from post-submission analyses.

## Index

### Research plans (forward-looking)

| File | Status |
|---|---|
| `research-plans/N1-cdcl-vs-beame-liew-gap.md` | Open. Replaces the obsolete `N1-exponential-lower-bound.md` in the authoritative repo (the original conjecture was refuted by Beame-Liew 2017/2019). Characterises why current CDCL doesn't find Beame-Liew's polynomial proofs, and what formula transformations enable it. |
| `research-plans/N3-beame-liew-implementation.md` | Advanced. Phase 1 + Phase 2 + Phase 3 (excluding final polynomial scaling) DONE. Validated at $n = 3 \ldots 6$ via `bench-multiplication/n3-beame-liew/phase3_full*.py`. Remaining: switch to CSA tableau or use RAT extensions for true polynomial scaling. |
| `research-plans/N4-multi-encoding.md` | Done. Multi-encoding ablation included in Paper 1 Appendix. Raw data in `data/multi-encoding-results.tsv` for any future re-analysis. |
| `research-plans/NEXT-STEPS.md` | Snapshot of Paper 1 + Paper 2 status as of 2026-05-12. Now partly stale (e.g., Paper 2 has had its senior-review pass). |

### Bug investigations / open issues

| File | Severity | Status |
|---|---|---|
| `refine-arithmetic-bypass-investigation.md` | High | **Fixed** in this session. The fix bit-blasts multiplications eagerly under `--refine-arithmetic` rather than lazily, eliminating the refinement loop's per-iteration SAT overhead while preserving pair detection's equality constraints. The submitted Paper 1 reflects the *pre-fix* behaviour. |

### Senior-reviewer report

| File | Description |
|---|---|
| `internal-review-2026-05-26.md` | Forward-looking senior-reviewer pass on the submitted Paper 1. 15 items at three severities. **Highest priority: item #1** (the §8 `--refine-arithmetic` overhead claim is now contradicted by the post-submission fix and must be updated in any revision). **Item #2**: §7.7 SMT-COMP framing understates a 33-vs-41 regression. **Item #3**: 21 pages is on the long side for PoS; cut list ready. The full list is the workbook for integrating peer-review feedback. |

### Post-submission data

| File | Description |
|---|---|
| `data/multi-encoding-results.tsv` | Multi-encoding ablation data (mirrored from Paper 1 N4 work). |
| `data/smt-comp-combacs-nosimp.tsv` | SMT-COMP sample with `comba-cs` encoding, simplification disabled (post-submission ablation). |
| `data/smt-comp-shiftadd-nosimp.tsv` | SMT-COMP sample with `shift-add` encoding, simplification disabled (post-submission ablation). |

## Open items for the next Paper 1 revision

These are items the senior-reviewer pass on Paper 2 surfaced or
that discoveries since 2026-05-11 have raised. They should be
considered when peer-review feedback arrives.

### Items requiring action (potentially)

1. **Senior-reviewer pass.** Paper 2 has had a structured senior-
   reviewer pass (see
   `~/cbmc-github.git/doc/paper-algebraic/internal-review-2026-05-18.md`).
   Paper 1 has had two earlier-style review passes but no
   equivalent end-to-front structured review. Worth doing once
   peer review feedback arrives so we can integrate both at once.

2. **Refinement-loop bypass bug fix.** See
   `refine-arithmetic-bypass-investigation.md`. When pair detection
   finds nothing, `--refine-arithmetic` still enters the legacy
   refinement loop and adds significant overhead. On 3 Martin
   benchmarks this causes T/Os where pure bit-blasting solves in
   ${<}1$\,s. The fix is implemented in this session (Option A:
   track pair-emission count, bypass loop when zero) but its
   empirical impact was not in the submitted Paper 1 numbers.
   When revising the paper post-peer-review, the wider three-pool
   comparison should be re-run with the fix to update headline
   numbers.

3. **Re-running the wide three-pool comparison.** With the
   refinement-loop fix in place, the existing numbers in
   `doc/wide-three-approach-comparison.md` (179 benchmarks, three
   pools, five configs; pair_detect 124, p2_algebraic 122, union
   140) will likely improve for `pair_detect` and `all_combined`.
   Worth re-running before any Paper 1 revision.

4. **Pair-detection writeup integration.** A 549-line technical
   writeup at `doc/pair-detection-paper-writeup.md` was prepared
   earlier in this session as candidate Paper 1 content. The
   submitted version of Paper 1 does NOT include this material
   in the form of an explicit pair-detection methodology section.
   **Open question for the authors:** whether this material should
   be folded into the Paper 1 revision (post-peer-review), or
   whether it belongs in a separate paper. If folded in, it would
   require:
   - integration with the existing encoding/methodology narrative;
   - a re-evaluation with the refinement-loop fix;
   - re-checking the ${\sim}$15-page page budget (PoS uses CEUR
     `ceurart.cls`).

   If kept separate, the pair-detection writeup needs its own
   target venue and structure.

### Items not requiring action

5. **Paper 2 changes that affect Paper 1 framing.** Paper 2 was
   significantly revised this session. None of those changes
   require Paper 1 to be updated, since Paper 1 cites Paper 2 only
   as `\cite{companion-bitblasting}` and the high-level framing
   is unchanged. (Paper 2 cites `companion-bitblasting` from its
   side, but Paper 2 is anonymised so the reference target is
   abstract.)

## Process

When peer review feedback arrives:

1. Read the feedback carefully. Compare it against the items in
   this loose-ends document. Items the reviewers flag take
   priority.
2. For items already in the loose-ends list that the reviewers
   did *not* flag, decide case-by-case whether to address them
   in the revision or defer to a separate paper / future
   iteration.
3. Once all changes are agreed, apply them to the authoritative
   copy in `~/multiplier-encodings.git/paper-bitblasting/`. Do not
   resurrect `cbmc-github.git/doc/paper-bitblasting/`.

If the user asks for any non-trivial changes to Paper 1's
`paper.tex` before peer review feedback arrives, push back: it's
generally best to wait so we can integrate feedback and our own
changes in a single coherent revision.