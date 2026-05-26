# Co-author Feedback on Paper 1 (2026-05-26)

*Date: 2026-05-26*
*Source: internal co-author read-through (in German, translated below)
plus a citation update from the lead author.*
*Status: to be acted on in the post-peer-review revision; complements
`internal-review-2026-05-26.md`.*

## 1. Co-author read-through (translated from German)

The original feedback was a mix of German and English; below is a
faithful English translation with each question or suggestion broken
out as a separate action item, ordered as in the original.

### Item C1 — Should we publish the full new comba-cs encoding?

> "Should we give the full new comba-cs encoding?"

**Question for revision**: do we include the complete formal
specification of the comba-cs encoding (clauses, partial-product
layout, second-pass carry handling, popcount blocks) in the body,
in an appendix, or as supplementary material?

The current paper.tex has Figure 1 (the high-level two-pass
diagram) and §5's prose description, but no clause-level encoding.
A reviewer wanting to reproduce or check encoding correctness
would need to read the source (`src/solvers/flattening/`).
Options:
- (a) Add a precise pseudocode appendix.
- (b) Cite a public artefact (the CBMC source) and leave the body
  prose-level.
- (c) A hybrid: pseudocode for the key invariant (carry separation
  + second pass), source citation for the rest.

Recommendation pending: probably (c), but a co-author decision.

### Item C2 — Stylistic: parenthetical asides

> "Stylistically, most of the parenthetical asides could probably
> be written without parentheses almost throughout."

**Editing pass.** Many sentences in the current paper.tex use
parentheses where regular subordinate clauses or separate
sentences would read more cleanly. Light copy-edit pass needed
on the post-peer-review revision; not a content change.

### Item C3 — Proof discussion: only the contributing parts?

> "When we talk about proofs, do we mean only the parts that
> contribute to the proof?"

**Clarification needed.** The DRAT-proof analysis we report (§4
methodology, §5 combacs) currently talks about "31% of all DRAT
steps" without distinguishing the *full* DRAT proof from the
*proof core* (the subset of steps actually needed to derive the
empty clause). Revisions could:
- Make the distinction explicit ("31% of all DRAT steps" vs "X%
  of proof-core steps").
- If only proof-core matters for the bottleneck argument, switch
  the headline number accordingly.

The proof-core measurement is a separate experiment (use a DRAT
trimmer like `drat-trim` or `cake_lpr` to extract the core).
Likely reveals tighter numbers and addresses the reviewer's
concern.

### Item C4 — Add columns to the DRAT table (Table 3)

> "Under the DRAT table (Table 3) we say 'less unit propagation'.
> Can we add a column there? Since we already have such a table,
> 'decisions' and 'conflicts' would also make sense, or
> proof-core size."

**Concrete table extension.** Current Table 3 (proof comparison
on commutativity BW=11) has four columns: standard Comba,
combacs, change. Reviewer suggests adding columns for:
- decisions (CDCL branching steps)
- conflicts (CDCL conflict count)
- proof-core size (after trimming)

Each is a one-line `solver.statistics()` query plus, for
proof-core, a `drat-trim` invocation. Effort: ~1 hour to gather,
plus space in the table.

### Item C5 — Reference for "4-bit block multiplication"

> "'4-bit block multiplication' — does that exist on GitHub as a
> reference?"

**Citation question.** §6.2 (4-Bit Block Multiplication)
attributes the encoding to "one of the authors (unpublished prior
to the present work)". A reviewer would want either a citation or
a public artefact pointer. Options:
- The encoding is implemented in CBMC (`src/solvers/flattening/`);
  a footnote pointing to a specific source file would give the
  reproducibility hook.
- If there's an unpublished tech report or preprint, cite that.
- Otherwise, the "unpublished prior to this work" framing is the
  truth and should stay, but with a code-pointer footnote.

### Item C6 — Adaptive-encoding-classifier scope

> "When best encoding depends on problem structure, do we have
> more than just multiplications in the input problem? Did we
> test anything else to implement such a classifier? Is that
> classifier CBMC-specific, or does it work in other SMT solvers
> as well?"

**Three sub-questions to address:**

1. **Input-formula scope.** §5.1 (Adaptive Encoding Selection)
   describes the classifier as triggered by the multiplication
   *count*, but the input problem can contain arbitrary other
   structure (bitwise, comparisons, ITE). The classifier's
   correctness when other operators are present is not
   discussed. Add a paragraph clarifying this.

2. **Alternative classifier designs tested.** §5.1 says the
   threshold is "insensitive (1, 4, or 99 produces identical
   results)". Did we test classifiers based on *features other
   than count* — e.g., bitwidth, presence of constants,
   syntactic structural matches? If yes, document them and the
   negative results. If no, mention this as a deliberate
   limitation.

3. **Solver portability.** The classifier currently fires inside
   CBMC's bit-blast layer. The question whether the same
   classifier would work in Bitwuzla / cvc5 reduces to: do those
   solvers expose enough of the encoding choice to plug in our
   adaptive logic? Probably not directly — the answer is "the
   classifier's logic is solver-agnostic, but its integration
   needs solver-specific plumbing". Worth a sentence.

### Item C7 — CryptoMiniSat inprocessing claim

> "Did you check CryptoMiniSat for the lack of inprocessing you
> mentioned (my knowledge is rusty, I assumed it's there)."

**Verify before next revision.** §7.3 says:

> cryptominisat is consistently the slowest on multiplication, as
> its native XOR handling provides no benefit … and it lacks both
> inprocessing BVE and congruence closure.

The reviewer's intuition is that CryptoMiniSat does have
inprocessing. **This is a factual claim we should verify in the
source** before submission. If wrong, the §7.3 explanation needs
to be re-thought (perhaps the issue is that CryptoMiniSat's
inprocessing is configured differently, or that congruence
closure is the missing piece on its own, not BVE).

Effort: ~1 hour to inspect CryptoMiniSat's source / docs /
default configuration.

### Item C8 — SMT-COMP QF\_BV sample as reference

> "Is the SMT-COMP QF\_BV sample good enough as a reference
> benchmark?"

**Open methodological question.** §7.7 evaluates on a
66-benchmark stratified sample of SMT-COMP 2024 QF\_BV. The
reviewer is asking whether this is the right reference.
Considerations:
- SMT-COMP benchmarks vary widely (some are multiplication-heavy,
  most are not).
- Stratified sampling controls for submitter bias but not for
  difficulty.
- A larger sample (e.g., the full ~16 000 multiplication-containing
  benchmarks) would be stronger but expensive.
- The current sample is a reasonable middle ground but the threats
  paragraph (§7.7) should make this explicit.

Possible action: add a paragraph defending the sample size /
stratification choice, or extend to a larger sample if reviewers
push.

### Item C9 — Appendix order

> "Does the appendix have a particular order?"

**Audit needed.** Current appendices:
- A. Layer Ablation: Full Table
- B. Multi-Encoding Experiment
- C. Adder Encoding Interaction
- D. Adaptive Heuristic Ablation
- E. BVE Interaction
- F. Encoding Comparison with Variance
- G. DRAT Proof Sizes Across Encodings

Is this order: (a) by which §X they support? (b) by importance?
(c) chronological? (d) ad hoc? Reviewer's question implies the
order is not obvious. A natural ordering would be by section
reference — the reader hits an appendix pointer in §X and finds
the appendix in §X order. Audit: walk through main-body forward
references and reorder accordingly.

### Item C10 — Tables need introductory sentences

> "From experience with Kiro: an introductory/explanatory sentence
> for the tables would probably help non-AI readers contextualise
> what's being shown."

**Direct feedback on AI-assisted drafting.** Tables in the paper
were drafted with AI assistance and tend to launch directly into
the data without prose context. A non-AI reader hits the table
and has to reverse-engineer what each column means. Recommendation:
each table caption should answer "what question does this answer?"
and the surrounding prose should make the table's role explicit.

This is a writing-style pass, ~2 hours across the paper. Concrete
example: Table 4 (allencodings) has caption "Four multiplier
encodings across four solvers" — fine. But the prose around it
jumps directly into the speedup discussion. A lead-in sentence
("Table 4 reports …, with the read order being …") would help.

## 2. Citation update — Beame & Sun 2026 now public

The Beame & Sun paper "Extending CDCL to disjunctions of parity
equations" (`~/sat-paper90.pdf`), previously read but
non-citable as it was unpublished work, is now publicly available
and citable:

- arXiv: https://arxiv.org/pdf/2605.15002
- Author: Paul Beame, Glenn Sun (University of Washington)
- Title: "Extending CDCL to disjunctions of parity equations"
- Subject: LIPIcs, Vol. 42
- Tool: Xorcle (https://github.com/glenn-sun/xorcle)

**What it claims.** Beame & Sun present CDCL($\oplus$), a
generalisation of CDCL to XOR-OR-AND Normal Form (XNF) formulas
whose constraints are disjunctions of parity equations. They
prove a bidirectional connection with Res($\oplus$): CDCL($\oplus$)
both produces Res($\oplus$) proofs and polynomially simulates
Res($\oplus$) given nondeterministic decisions and restarts ---
mirroring the classical CDCL/Resolution relationship. Their
implementation Xorcle outperforms Kissat and CryptoMiniSat on a
selected XNF benchmark suite.

**Where to cite in Paper 1.** The current paper.tex already cites
Danner 2025 (`danner2025sat`) in the §10 "Escaping resolution
hardness in CDCL" paragraph, which discusses CDXCL (Danner's
CDCL generalisation to XNF). The Beame & Sun paper is the
*independent* algorithmic / proof-theoretic development of the
same problem space; both should be cited together. Concrete
revision item:

In paper.tex line ~1339 (the (ii) point of the "Escaping
resolution hardness" paragraph), expand:

> (ii)~Solver-level generalisation to stronger proof systems:
> Danner's dissertation~\\cite{danner2025sat} develops CDXCL,
> a CDCL generalisation to XOR-OR-AND Normal Form (XNF) clauses
> ...

to also cite Beame & Sun's CDCL($\oplus$) and Xorcle, mentioning
the bidirectional Res($\oplus$) simulation result and that two
independent groups (Passau / UW) reached similar conclusions
about the proof-system generalisation.

A bib entry to add to `references.bib`:

```bibtex
@article{beame2026cdcl,
  author    = {Paul Beame and Glenn Sun},
  title     = {Extending {CDCL} to Disjunctions of Parity Equations},
  journal   = {LIPIcs},
  volume    = {42},
  year      = {2026},
  url       = {https://arxiv.org/abs/2605.15002},
  eprint    = {2605.15002},
  archivePrefix = {arXiv}
}
```

The exact venue (`LIPIcs Vol. 42`) suggests a CCC / SAT-track
proceedings; verify before final submission. The eprint number
should also be confirmed against arxiv.org's listing for typo
safety.

## Process

These items are **deferred**: they will be picked up alongside
peer-review feedback (expected ~2026-06-02) when revising the
paper. None of them are blocking; all are content / wording
improvements that fit naturally into the response-to-reviewers
phase.

When peer-review feedback arrives:
1. Add reviewer comments to the existing
   `internal-review-2026-05-26.md` workbook.
2. Cross-reference these co-author items: where reviewer and
   co-author feedback overlap, address once.
3. Where they don't overlap, treat the co-author items as a
   secondary checklist for the revision.
