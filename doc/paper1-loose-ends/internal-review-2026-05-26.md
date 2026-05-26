# Senior Reviewer Report on Paper 1

*Date: 2026-05-26*
*Persona: senior scientific reviewer*
*Reading mode: end-to-front, multi-pass*
*Paper version reviewed:* `~/multiplier-encodings.git/paper-bitblasting/paper.tex`
*at commit 1fe9b72 ("Submitted version", 2026-05-11)*
*Length: 21 pages, 47 references; submitted to Pragmatics of SAT (PoS)
2026, currently under peer review.*

## Context for this review

Paper 1 has been submitted to PoS and is currently under peer
review (feedback expected ~ 2026-06-02). **This review is
forward-looking**: it documents issues a co-author or external
reviewer might raise, so we can address them coherently when peer
review feedback arrives. **No changes have been made to
`paper.tex`** as part of this review --- per the user's
instruction, any post-submission modifications stay in
`doc/paper1-loose-ends/` until peer review feedback arrives.

PoS is **non-anonymous** (CEUR `ceurart.cls` permits author info),
so the anonymisation issues that dominated the Paper 2 review do
not apply here. Author list, ORCID, and AI-assistant declaration
are all already in the manuscript.

## Status of items (forward-looking)

All items below are TODO until peer review feedback arrives. The
table below is meant to be merged with reviewer comments rather
than acted on in isolation.

| #  | Issue | Severity | Effort |
|---|---|---|---|
| 1  | `--refine-arithmetic` overhead claim in §8 is now stale | High | 30 min once allowed to edit |
| 2  | §7.7 SMT-COMP framing "nearly neutral" understates a slight regression | High | 20 min |
| 3  | Length: 21 pages; CEUR `ceurart` papers are typically 12–15 | High | 1–2 hours |
| 4  | "Methodology" framing of §4 is one case study, presented as a procedure | Medium | 1 hour to reframe |
| 5  | §3 GF(2) experiment scope statement is good; the overstating risk remains | Medium | 30 min |
| 6  | §5 adaptive-heuristic robustness ("threshold 1, 4, or 99 identical") under-emphasised | Low | 10 min |
| 7  | §6 Table `tab:best` is the spine of "no encoding dominates" but tucked at the end of §6 | Medium | 30 min |
| 8  | §7 has 7 subsections; some overlap (industrial vs custom both have CBMC-style) | Medium | 1 hour |
| 9  | "44 benchmarks" terminology vs §7 Table showing only 9 representatives is confusing | Low | 15 min |
| 10 | Pair-detection is implemented in CBMC but not documented in this paper | Open | structural decision |
| 11 | bf16 results show only `bf16_mul_comm_v2`; v1 not compared in main tables | Low | 30 min |
| 12 | "keyed hash determinism" 5× regression is honestly reported but minimised in prose | Low | 10 min |
| 13 | Abstract is long (25 lines, dense); the GF(2) controlled-experiment description could move to body | Low | 20 min |
| 14 | §1 "deployment configuration" footnote duplicates §7.2 paragraph "Context: algebraic pre-solver disabled" | Low | 10 min |
| 15 | Per-paragraph anchor language ("nearly neutral", "honest reading") not used consistently | Low | 20 min |

## Critical issues (high severity)

### 1. The `--refine-arithmetic` overhead claim in §8 is now stale

Section 8 (Negative Results) states:

> CBMC's CEGAR loop (`--refine-arithmetic`) adds $\geq$2 solver
> calls of overhead on UNSAT benchmarks (commutativity BW=11:
> 4.0 s vs. 0.9 s direct combacs).

This was true at submission time. Since then a refinement-loop
bypass fix was implemented (this session, see
`refine-arithmetic-bypass-investigation.md`); under
`--refine-arithmetic` we now eagerly bit-blast multiplications and
the loop converges in one iteration. Empirical re-test on the same
benchmark family (Martin's bw=8 polynomial-identity sample): the
fix turns 3 timeouts into solves at $0.05$–$0.12$ s, faster than
shift-add bit-blasting alone.

This means the §8 sentence may be **flat-out contradicted** by
external researchers running our public CBMC. Two options for the
revision:
- Update the §8 sentence to reflect the fix and the new empirical
  picture: "`--refine-arithmetic` adds no measurable overhead on
  UNSAT benchmarks since the recent eager-bit-blast bypass; in
  earlier versions it added $\geq$2 solver calls."
- Or remove the §8 sentence entirely and replace with a forward
  pointer to the fix in supplementary material.

Either way, the headline "approaches that hurt" claim about
`--refine-arithmetic` is no longer supported.

### 2. §7.7 SMT-COMP framing understates a slight regression

Table `tab:smtcomp-sample` shows:
```
shift-add-nosimp (smt2_solver) 41/66
combacs-nosimp   (smt2_solver) 41/66
default          (algebraic + combacs, cbmc)  33/66
```

The accompanying prose says: "our changes are *nearly neutral on a
broad QF\_BV community sample*: they are not a silver bullet, nor
are they a regression."

But the default configuration (33) is *8 fewer* than the
encoding-only baseline (41). That is not "neutral" --- it is a
20% regression in solved count, masked because the comparison the
prose emphasises is rows 1 vs 2 (encoding only, both 41).

The truthful framing is more like:
- Encoding choice (combacs vs shift-add) is neutral on this
  sample, with the per-benchmark ratio in $[0.83, 1.15]\times$.
- The full pipeline (algebraic + combacs via cbmc) loses 8
  benchmarks compared to the bit-blasting baseline, primarily
  on `bvudiv`/`bvsdiv`-dominated benchmarks where the algebraic
  layer's GCD rewriting expands the formula. This is consistent
  with our claim that the techniques target arithmetic-identity
  patterns, not general QF\_BV.

The current framing risks a reviewer flagging this as "selective
reading of own data". The 33-vs-41 number deserves explicit
acknowledgement, not just a parenthetical "default's effect on a
handful of benchmarks".

### 3. Length: 21 pages

CEUR `ceurart.cls` does not have a hard page cap, but PoS papers
typically run 12--15 pages. 21 is on the long side. PoS reviewers
often comment on length when sections feel like they could be
appendix material.

Candidates for cuts (~5 pages):

| Section / content | Pages saved | Risk |
|---|---|---|
| §6.2 (4-Bit Block Multiplication) — currently 2 paragraphs of methodology + 1 result. The result lives in §7 already. | 0.3 | Low |
| §7.5 (Industrial Benchmarks) — 5 benchmarks in a table; could move to appendix | 0.4 | Low |
| §7.6 (Custom Benchmarks in SMT-LIB) — overlaps significantly with §7.4 (scaling) and §7.7 (SMT-COMP); merge or move to appendix | 0.6 | Medium |
| §8 (Negative Results) — currently 4 paragraphs covering many distinct experiments; could be tightened | 0.5 | Low |
| §9 (Related Work) — currently 7 paragraphs; the algebraic, gate-level algebraic, and word-level paragraphs could merge | 0.7 | Low |
| Appendix B (Multi-Encoding Experiment) — already framed as "for completeness"; consider removing | 0.5 | Low |
| Appendix F (Encoding Comparison with Variance) — variance argument made in prose; full table redundant | 0.4 | Low |
| §3 (Hardness) §3 controlled experiment — Table 2 is fine, but the surrounding prose could be tighter | 0.3 | Low |

That's ~3.7 pages. To get to ~5 we'd need a structural decision on
§7's seven subsections.

## Important content/structure issues (medium severity)

### 4. "Methodology" framing of §4 is one case study, presented as a procedure

§4 is titled "Designing combacs through DRAT Analysis" and §1
contribution 1 calls it "a DRAT-guided design case study". §4 then
gives a numbered 6-step procedure:

> 1. Generate a DRAT proof
> 2. Count variable participation
> 3. Trace the top variables
> 4. Hypothesise a structural cause
> 5. Propose an encoding modification
> 6. Validate

The 6 steps were applied **once** (combacs). The other three
encodings (Booth, block4, sortnet) are presented as
"retrospective analysis" --- the methodology *explains* their
behaviour but did not produce them.

The §1 contribution 1 already acknowledges this honestly: "this is
a detailed case study, not a general methodology claim". But §4 is
still framed as if it's a transferable methodology. A reviewer
might ask: "if this is a methodology, why was it applied only
once?" and "if it's a case study, why is it numbered as a
procedure?"

Recommendation: either commit to "methodology" framing and apply
the 6 steps explicitly to one of the retrospective encodings (even
briefly), or drop the numbered procedure in favour of a
description of the case study with the lessons learned.

### 5. §3 GF(2) experiment scope statement

§3 has the GF(2)-vs-integer comparison + a controlled five-variant
experiment. The "scope" paragraph at the end is well-handled:

> **Scope.** The experiment establishes that on commutativity and
> on cadical, carry presence dominates the choice of accumulation
> topology; it does not establish a proof-theoretic lower bound,
> given the Beame--Liew upper bounds cited above.

This is good. But the rest of §3 still uses "carry propagation
hardness" framing. A careful reader might wonder: how can
carry propagation be "the dominant driver of CDCL search
difficulty" when polynomial proofs exist?

The §3 paragraph "The gap is between proof existence and CDCL
search" handles this directly. But it's buried in the middle of
§3. Consider promoting that paragraph to the top of §3 so the
"empirical hardness for current CDCL" framing is established
before the GF(2) data.

### 6. §5 adaptive-heuristic robustness under-emphasised

The §5 paragraph says:

> The multiplication count threshold is insensitive: changing it
> from 2 to 1, 4, or 99 produces identical results because cbmc's
> word-level algebraic pre-solver subsumes the threshold's
> purpose for polynomial benchmarks, and non-polynomial
> benchmarks in our suite have $\leq$2 multiplications.

This is a **strong** robustness claim --- the heuristic is not
hyperparameter-sensitive. Currently buried mid-paragraph.
Recommendation: either move to its own sentence with an emphasis
("the heuristic is parameter-free in practice") or call it out as
a footnote.

### 7. §6 Table `tab:best` is the spine of the "no encoding dominates" claim

Table `tab:best` ("Best encoding per benchmark class") summarises
the paper's biggest claim. It's at the end of §6.3 ("No Single
Encoding Dominates"), with a 5-row mechanistic explanation
following.

Recommendation: this should be promoted to its own subsection
heading, perhaps with a slightly bigger / restructured table that
also shows numerical evidence per row. The current presentation
makes it easy to skim past.

### 8. §7 has 7 subsections; consolidate

Current §7:
- 7.1 Layer Ablation
- 7.2 Multiplier Encoding Comparison
- 7.3 Cross-Solver Analysis
- 7.4 Scaling
- 7.5 Industrial Benchmarks
- 7.6 Custom Benchmarks in SMT-LIB Format
- 7.7 SMT-COMP QF\_BV Community Sample

7.5, 7.6, 7.7 are all "evaluations on more benchmarks". Could be
consolidated to two subsections (or moved partly to appendix).
The current organisation reflects what the experiments *were*
rather than what story they tell.

A possible restructure:
- 7.1 Encoding ablation (combines current 7.1, 7.2, 7.3)
- 7.2 Scaling (current 7.4)
- 7.3 External validity (current 7.5--7.7, condensed)

This more directly mirrors the contribution claims.

## Polish / consistency issues (low severity)

### 9. "44 benchmarks" / "9 benchmarks" inconsistency

§7 introduction says benchmarks are "extended to 44 with eight DSP
datapath benchmarks". §7.6 starts: "we evaluate on 44 QF\_BV
benchmarks". But Table `tab:qfbv` shows only 9 rows.

The 9 rows are explicitly representatives ("combacs wins (2-mul
commutativity, popcount)" etc.) but the section reads as if those
are the entire suite. Either show all 44, summarise as "9
representatives of 44", or move the full table to appendix.

### 10. Pair-detection is implemented in CBMC but not documented in this paper

A 549-line writeup of algebraic-pair detection
(`doc/pair-detection-paper-writeup.md`) exists in the working
repo. It's not in the submitted paper. The user has flagged this
as an open question in the loose-ends README: should it be folded
into Paper 1's revision, or be its own paper?

**Reviewer's recommendation:** keep it as its own paper.
Pair-detection is conceptually distinct from encoding choice (it
asserts equality between different multiplications, regardless of
which encoding is used for each), and Paper 1 is already at the
length limit. Folding pair-detection in would require expanding
§5 substantially and would dilute Paper 1's tight encoding-and-
methodology focus. The natural pairing for pair-detection is
*Paper 2*, but Paper 2 is double-blind and already submitted to
TACAS 2027, so that ship has sailed for the current revision.
Pair-detection deserves its own venue.

### 11. bf16 results show only v2

bf16_mul_comm appears in Tables and prose only as
"bf16_mul_comm_v2" (the harder variant). Some readers may wonder
about v1; mentioning the difference once would help.

### 12. "keyed hash determinism" regression minimised

Industrial benchmarks Table 8 shows combacs makes
keyed-hash 5× slower (1.3 s → 6.5 s). The accompanying prose:

> The keyed hash regression (1.3 s → 6.5 s) is from constant
> multiplication where the adaptive fallback routes through
> dadda-cs instead of shift-add; the benchmark remains fast in
> absolute terms.

The "fast in absolute terms" softens what is a real 5× slowdown.
A reviewer might ask: why didn't the adaptive heuristic detect
constant multiplication and route to shift-add instead of
dadda-cs? Worth answering explicitly.

### 13. Abstract is long and dense (25 lines)

The abstract packs methodology + GF(2) controlled experiment +
comparison + adaptive selection. PoS abstracts can usually be
tighter (15--20 lines). The detailed GF(2) controlled-experiment
description (5 lines) could move to §1; the abstract could
state the result ("$\geq 1000\times$ harder at BW=12") without
the experiment design.

### 14. §1 "deployment configuration" footnote duplicates §7.2 prose

§1 (after the 4-contributions list) says:

> For this paper the algebraic pre-solver is disabled, isolating
> the encoding's contribution. In the deployed configuration, the
> encoding matters primarily for problems the algebraic layer
> cannot handle: bitwise operations, inequalities, floating-point,
> and structural mismatches.

§7.2 has a near-identical paragraph "Context: algebraic pre-solver
disabled". One can be deleted; pick the one that fits its section
better (probably §7.2, since that's where the comparison actually
is).

### 15. Per-paragraph anchor language not used consistently

Paper 2 uses "Honest reading" and "Methodological caveat" headers
in its evaluation section. Paper 1 uses similar phrasing
inconsistently: "Threats to validity" appears twice (§7.6 and
§7.7), "Robustness" once, "Context: algebraic pre-solver
disabled" once. Consider standardising.

## Strengths to preserve

- **Honest reporting.** Multiple "threats to validity"
  paragraphs, the "no single encoding dominates" thesis, the
  negative results section.
- **Beame--Liew framing.** §3's positioning of empirical hardness
  vs.\ proof existence is the strongest framing in the paper.
  Carries the methodology section, the related work positioning,
  and the conclusion's call to action ("encoding-level guidance"
  alongside CDXCL and CaDiCaL-FX).
- **Cross-solver evaluation.** Four solvers, with mechanistic
  explanations of why each one responds the way it does.
  Particularly strong because the explanations connect to specific
  solver features (BVE, congruence closure, XOR handling).
- **Appendices give reproducibility without bloating body.**
  Layer ablation full table, multi-encoding experiment, adder
  encoding interaction, BVE sensitivity, variance, proof sizes.

## Summary recommendation

**Highest priority items for the revision once peer review
feedback arrives:**

1. **#1 (refine-arithmetic stale claim)** --- factually
   contradicted by post-submission code; must update.
2. **#2 (SMT-COMP framing)** --- a careful reviewer will catch
   this; better to fix it ourselves first.
3. **#3 (length)** --- depends on whether reviewers flag it. If
   they do, we have a clear cut list.

**Decisions to defer until peer review feedback arrives:**

4. **#10 (pair-detection in or out of Paper 1)** --- recommend
   *out*, but ultimately a co-author decision.
5. **#4 (methodology vs case study framing)** --- if reviewers
   like the methodology framing, keep it; if they push back,
   reframe as a case study.
6. **#7--#8 (presentation restructure)** --- if reviewers find
   §7 too dense, the cuts are ready.

**Items that can be addressed in any revision regardless of
feedback:**

7. **#5, #6, #9, #11–#15** are polish, can be applied any time.

## Process

When peer review feedback arrives:

1. Compare the reviewer comments against this report.
2. Items the reviewers flag take priority.
3. For items in this report that reviewers did *not* flag:
   - Critical (#1, #2): apply unilaterally, document in the
     response letter.
   - Important (#3 cut list, #4 framing): apply only if needed
     to address other reviewer concerns.
   - Polish (#5–#15): apply opportunistically as the response
     letter is drafted.

This report is a co-authoring artefact; if peer review feedback
disagrees with any of these recommendations, the reviewer's
feedback wins.
