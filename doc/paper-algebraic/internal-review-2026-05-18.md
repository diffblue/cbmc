# Senior Reviewer Report on Paper 2

*Date: 2026-05-18*
*Persona: senior scientific reviewer*
*Reading mode: end-to-front, multi-pass*
*Paper version reviewed: commit `b2a801665a` (23 pages)*

## Status of items (updated 2026-05-26)

| Item | Status | Commit |
|---|---|---|
| #1 Anonymisation breaks (Mathlib PR #38628) | TODO | — |
| #2 Length: 23 pages → cut 5–7 pages | TODO | — |
| #3 Abstract is misleading (missing SMT-COMP datapoint) | **FIXED** | (current session) |
| #4 ZFP terminology inconsistent | **FIXED** | (current session) |
| #5 Completeness claim vs §6 future-work line | **FIXED** | (current session) — implementation already supports mixed widths; §6 line removed; §3.2 strengthened with explicit "Mixed input widths" paragraph documenting the capability and citing two benchmarks (dsp_image_reject and dsp_vanishing_mv) |
| #6 §3 completeness claim vs §4.5 SAT-finding losses | **FIXED** | (current session) — added "Direction of completeness" paragraph in §3 explicitly stating the algebraic layer is UNSAT-oriented |
| #7 Table 1 shows only 11/39 benchmarks | TODO | — |
| #8 §2.6 5-layer pipeline table confusing | TODO | — |
| #9 §2.7 shift-add comparison unfair | **FIXED** | (current session) — added Bitwuzla column to Table 2; rephrased framing to acknowledge mature word-level reasoners also handle these identities; updated abstract and §1 opener to remove the misleading "four orders of magnitude" claim |
| #10 §2.3 contribution list awkward | **FIXED** | (current session) — consolidated 6 points into 3 grouped contributions: SMT integration, algorithmic refinements, mechanised soundness |
| #11 Methodology inconsistency (median of 3 vs 5) | TODO | — |
| #12 'Honest reading' paragraphs scattered | TODO | — |
| #13 §1 four-classes taxonomy too long | TODO | — |
| #14 §6 conclusion repeats abstract | TODO | — |
| #15 Tables 4+5 should be one figure | TODO | — |
| #16 §5 Mechanised Soundness Lean technical detail | TODO | — |
| #17 Table footnote markers in LNCS | TODO | — |
| #18 §4.5 'n' header clashes with §3 'n' | TODO | — |

## Overall assessment

A solid paper with two clear technical contributions (Gröbner over
$\mathbb{Z}_{2^d}$ and vanishing-polynomial test), strong honesty
about limitations, and a credible empirical evaluation. But it
currently reads as **two papers stitched together** at 23 pages, and
several issues need attention before internal review or external
submission.

## Critical issues (must address before any submission)

### 1. Anonymisation breaks — double-blind violation

The paper is supposed to be double-blind. The following will identify
the authors instantly:

- **§5 (Mechanised Soundness):** "(Submitted to Mathlib as PR #38628.)"
- **§6 (Data availability):** "Mechanised Lean 4 proofs of soundness
  are distributed with the artifact and submitted as PR #38628 to
  Mathlib."
- **§2.3 (Contributions beyond Song et al.):** "including a new
  Mathlib contribution (PR #38628) on the unit characterisation of
  $\mathbb{Z}_{2^d}$."

PR #38628 is publicly attributed on GitHub. **Anyone looking up the
PR sees the authors.** Replace with anonymous phrasing throughout:
"a Mathlib contribution under review, identifying details withheld
for double-blind review."

The `brain2025subpoly` bib entry is correctly anonymised — same
treatment is needed for the Mathlib PR.

### 2. Length: 23 pages → typical LNCS conference cap is 15–16 pages + references

You'll need to cut roughly **5–7 pages** for a TACAS-style LNCS
submission. The paper is currently the length of a journal paper,
not a conference paper.

The cleanest cuts:

| Cut                                                                              | Pages saved | Risk |
|---|---|---|
| Move §2.5 worked example (BW=3 commutativity) → appendix                         | ~0.5 | Low — pedagogical only |
| Move §3.4 worked example (4x²+4x ≡ 0 mod 8) → appendix                          | ~0.5 | Low — pedagogical only |
| Condense §3.3 paragraph "Why a separate test instead of ZFPs" to a footnote      | ~0.5 | Low |
| Condense §2.4 ordering ablation (Table 3 + commentary) into one paragraph        | ~0.5 | Low — main message is "ordering doesn't matter" |
| Move §4.4 Amulet2 comparison → appendix or trim by half                          | ~1.0 | Medium — provides scope clarification |
| Move §4.5 (Random Polynomial Identity Suite) → appendix or trim to one paragraph | ~1.5 | Medium — recently added, could be supplementary |
| Merge Tables 4 + 5 (degree scaling, varscale) into a single figure               | ~0.5 | Low |
| Trim §6 future-work paragraph "Towards a true theory solver" from 18 lines to 5  | ~0.5 | Low |

That's about 5 pages saved.

### 3. Abstract is misleading

Abstract says: "On our 39-benchmark arithmetic-identity suite, CBMC
solves all 39 instances; cvc5 solves 35/39 (failing only on bfloat16…)"

But §4.2 (SMT-COMP 2024 sample) shows: "cvc5 default 38/66, shift-add
CBMC 34/66, default CBMC 33/66."

The custom suite is biased toward our strengths (you correctly
disclose this in §4.6 Threats to Validity), so leading the abstract
with the 39/39 result without the SMT-COMP datapoint is **selective
reporting**. Add one sentence: "On a 66-benchmark stratified SMT-COMP
2024 sample, our combined approach matches or slightly trails mature
word-level reasoners (33/66 vs cvc5's 38/66 and shift-add
bit-blasting's 34/66), confirming our techniques are a complementary
fast path rather than a general replacement."

## Important content/structure issues

### 4. The "ZFP" terminology is inconsistent across the paper

§3 introduces "zero-function polynomials (ZFPs)" prominently. §2
doesn't mention them. §1 abstract doesn't mention them. §6 conclusion
mentions "vanishing polynomial" but not "ZFP."

Decision: either commit to ZFP throughout (rename §3 to "Zero-Function
Polynomial Test"), or drop the ZFP framing and stay with "vanishing
polynomial test" everywhere. Right now it looks like a recent-revision
artefact.

### 5. The completeness claim in §3 needs softening

§3.3 says: "The test is complete for polynomial equivalence over
$\mathbb{Z}_{2^{n_1}} \times \cdots \times \mathbb{Z}_{2^{n_d}}
\to \mathbb{Z}_{2^m}$."

But §6 future work admits: "the vanishing polynomial test currently
handles same-width inputs; extending to mixed widths… would broaden
applicability."

These contradict each other. If your implementation only handles
same-width, §3.3 should say: "the test is complete for the same-width
case ($n_1 = \cdots = n_d = m$); extension to mixed widths is
straightforward but outside our current implementation."

### 6. The "completeness" claim in §3 vs the §4.5 SAT-finding losses

§3 frames the vanishing polynomial test as "complete for the
equivalence fragment." §4.5 honestly reports 8 SAT-finding losses to
bit-blasting on Martin's benchmarks. These don't directly contradict
(the claim is for UNSAT-direction equivalence checking, the losses
are SAT-finding queries), but the reader doesn't get this nuance from
§3 alone.

Add one sentence at the end of §3 introduction: "The test (and the
Gröbner basis solver more broadly) is UNSAT-oriented: it proves that
two polynomials are equal as functions, but cannot find a witness
when they differ. SAT-finding queries (`does p(x) = c have a
solution?`) require the bit-blast layer (Section 4.5)."

### 7. Table 1 only shows 11 of 39 benchmarks

The "External solver comparison" table shows 3 polynomial cases, 4
bf16 wins, 3 Bitwuzla wins, then a summary line. Where are the other
28? A reader can't verify the 39/39 claim or see distribution of
timings.

Recommendation: either show all 39 (compactly) or move detailed
per-benchmark to appendix and just give summary statistics here
(median, min, max, T/O count per solver).

### 8. §2.6 "Solver Pipeline" Table (5-layer pipeline)

The "CBMC vs smt2" two-column structure with dashes and footnote
markers is confusing. The dashes mean "doesn't apply" but the table
reads as if data is missing. The "0.000 s" entries also stretch
credulity (should be e.g. "<1 ms" with a note about resolution).

Recommendation: pick one column (smt2 is fairer since it doesn't
conflate front-end simplification), keep the layer structure, and add
the smt2 timings only.

### 9. The shift-add comparison is unfair

§2.7 (Bitwidth Independence) Table 2 compares the algebraic solver to
"comm (SAT, shift-add)" which T/Os at BW=16. But shift-add is a
deliberately bad encoding for commutativity (no CSE). The fair
comparison is the algebraic layer vs **Bitwuzla** at large bitwidths.

This argument also appears in §6 conclusion: "speedup of over
$2.6 \times 10^4$ from bit-blasting to algebraic." Reading: this is
$2.6 \times 10^4$ from CBMC's worst encoding, not from Bitwuzla's
word-level rewriting (which would handle commutativity in
microseconds via syntactic normalisation).

Recommendation: in §2.7, either add a Bitwuzla column to Table 2, or
weaken the claim: "the algebraic procedure scales independently of
bitwidth, in contrast to bit-blasting under our shift-add encoding
(which times out at BW=16) — Bitwuzla's word-level rewriting also
handles these identities efficiently via syntactic methods
(Section 4.1)."

### 10. §2.3 "Contributions Beyond Song et al." has 6 numbered points with extensive prose

The list is good, but enumerating six distinct contributions in 30
lines of prose, then saying "none individually is a standalone
research result," is awkward. It also makes the contribution-list
look weak (6 small ones rather than 1–2 big ones).

Recommendation: consolidate into 3 contributions:

1. **End-to-end SMT integration** (covers points 1, 3 — the
   engineering of getting Gröbner working inside CBMC).
2. **Algorithmic refinements** (points 2, 4, 5 — Rabinowitsch,
   progress termination, candidate extraction).
3. **Mechanised soundness** (point 6).

Each gets one paragraph. Total ~12 lines instead of 30.

## Minor / polish issues

### 11. Methodology inconsistency

- §2.7: "mean of 5 runs each, discarding the first 'cold' run."
- §3.3 Empirical degree scaling: "median of 3 runs."
- §3.3 varscale: "median of 3."

Pick one and use it consistently. "Median of 5, first discarded" is
fine; "median of 3" is too few for stable measurements at the
millisecond scale.

### 12. The "honest reading" / "methodological caveat" paragraphs are scattered

Multiple sections have similar disclaimers:
- §4.1: "Methodological caveat: 5 DSP benchmarks designed by us..."
- §4.3: "Honest reading. On this community set Bitwuzla beats us..."
- §4.6: full Threats to Validity section.

Recommendation: consolidate per-section caveats into §4.6, OR drop
§4.6 and rely on the per-section caveats. Don't have both.

### 13. §1 four-classes-of-query taxonomy is 12 lines for a single point

The (universal-equational, existential-equational, universal-relational,
existential-relational) taxonomy is interesting but uses ~12 lines to
say "we focus on universal equational, the companion paper handles
the others." Could be 4 lines: "Bit-vector multiplication queries
split by quantification (universal vs existential) and connective
($=$ vs $\neq$/$<$). Algebraic methods excel on universal equational
queries; the others are handled by bit-blasting."

### 14. §6 Conclusion repeats abstract numbers

The first paragraph of conclusion restates "<5 ms regardless of
bitwidth," "<15 ms," "39/39," "35/39," "33/66 vs 34/66 vs 38/66." All
in the abstract. Trim to: "We presented two algebraic techniques...
Empirical evaluation across three benchmark pools shows the technique
is a fast path for arithmetic identities and a complementary layer to
mature word-level reasoners; details in §4."

### 15. Tables 4 (degree scaling) + 5 (varscale)

Both tables are about scaling. Table 4 has 2 BW-rows × 5 k-values.
Table 5 has 5 k-values × 5 columns including a multirow. Could be one
log-log plot showing both scaling curves on one figure (~0.3 page)
instead of two tables (~0.7 page).

### 16. The §5 Mechanised Soundness section is short (24 lines) but lists key technical detail

The "key technical challenge was numeral elaboration in `ZMod`"
sentence is interesting but probably belongs in an artifact-companion
document, not the paper. Cut and gain a few lines.

### 17. Table 1 footnote markers (`*`, `†`)

The asterisk and dagger footnotes in Tables 1 and 2 are tucked at the
bottom of the table. In LNCS templates these often render awkwardly.
Move to caption or to the surrounding prose.

### 18. The "Random Polynomial Identity Suite" (§4.5) has a per-category table that's good but uses "n" for category size

The header `n` could clash with the polynomial variable `n` used in
§3. Rename to `|cat|` or "size" for clarity.

## Summary recommendation

**Before any internal review:**

1. Fix the Mathlib PR anonymity issue (5-minute fix, 3 places).
2. Add the missing SMT-COMP datapoint to the abstract (one sentence).
3. Soften the "complete" claim in §3 to mention same-width
   restriction.

**Before external submission:**

4. Cut ~5 pages following the schedule above. The natural appendix
   candidates are: worked examples (§2.5, §3.4), Amulet2 detail
   (§4.4), Random Polynomial Suite detail (§4.5), and the "Why not
   ZFPs" paragraph (§3.3).
5. Decide whether to keep "ZFP" terminology and use it consistently.
6. Consolidate the §2.3 contribution list into 3 grouped
   contributions.
7. Reconcile timing methodology across the paper.
8. Fix the shift-add comparison framing in §2.7.

**Strengths to preserve:**

- The honest reporting style — keep the §4 caveats.
- The Lean 4 verification — major differentiator.
- The negative-result content (ZFP injection, Amulet at 128+ bits).
- The clean separation of contribution from Song et al.

This paper has a real contribution. The main work needed is
**trimming and tightening** rather than adding content.
