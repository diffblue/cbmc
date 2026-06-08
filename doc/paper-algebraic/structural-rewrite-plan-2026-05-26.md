# Paper 2 Structural Rewrite Plan

*Date: 2026-05-26*
*Status: draft, not yet applied to `paper.tex`*
*Target submission: TACAS 2027, deadline 15 Oct 2026*
*Current paper.tex: 1493 lines, 24 pages, 0 undef refs.*

This plan complements the bug-level review in
`internal-review-2026-05-18.md` (which fixed local issues) and
addresses storytelling-level structural problems. The 18-item review
addressed *what was wrong sentence-by-sentence*; this plan addresses
*what is wrong section-by-section*.

The plan is sequenced from low-risk reframing (text only, no
benchmark changes) to high-risk restructuring (table reorganisation,
section moves). All tasks are reversible.

## Status

| #  | Task | Severity | Effort | Risk |
|---|---|---|---|---|
| R1 | Re-centre the contribution on the 18 algebraic-only wins + DSP function equivalence | Critical | 4 hours | Low |
| R2 | Distinguish ideal membership vs function equivalence consistently | Critical | 2 hours | Low |
| R3 | Promote four-classes taxonomy to the organising scaffold | Critical | 4 hours | Medium |
| R4 | Lift Lean → C++ feedback (progress termination) to a contribution | Important | 1 hour | Low |
| R5 | Reframe vanishing-polynomial test as headline, not remediation | Important | 2 hours | Low |
| R6 | Reorganise §7 evaluation by taxonomy class | Important | 3 hours | Medium |
| R7 | Streamline §9 related work by taxonomy class | Important | 2 hours | Low |
| R8 | Strip hedging language ("complementary", "matching", "fast path") | Polish | 1 hour | Low |
| R9 | Move "Towards a true theory solver" from §10 conclusion to §3.2 future-direction within scope | Polish | 30 min | Low |
| R10 | Tighten §1 (commutativity hook is a hidden weakness) | Polish | 1 hour | Low |

Total effort: ~20 hours. None of this is "do experiments";
all of it is reframing existing content.

## Diagnosis (recap from oral review)

The paper's technical content is solid: a Gröbner-basis solver
over $\mathbb{Z}_{2^d}$ with progress-based termination, a
vanishing-polynomial test using falling factorials and Kronecker
products, 25 Lean 4 theorems, integration into CBMC, and three
benchmark pools.

What does not work:
1. The pitch keeps shifting across abstract / §1 / §3 / §7 / §10.
2. The opening hook (commutativity at BW=16) is a *weakness*
   dressed up as a strength — Bitwuzla already does this, faster.
3. The strongest result (18 algebraic-only wins on the random
   polynomial suite, where bit-blasting cannot encode the
   multiplications within 10 s) is the fifth sub-evaluation.
4. Vanishing polynomials are framed as "remediation for
   incompleteness" instead of as an original contribution.
5. The Lean → C++ feedback story (formalisation forced us to
   isolate "progress", which removed a 2000× ordering sensitivity)
   is hidden in a methodology subsection.
6. The four-classes taxonomy is decorative.
7. Hedging language ("complementary fast path", "matching mature
   reasoners", "competitive on simple identities") signals that
   the authors are not committing to the contribution.

## Re-centring (R1, R2, R5)

### What the paper is actually claiming (when claims are aligned)

> **There exist polynomial identities and function equivalences in
> bit-vector arithmetic that no current SMT solver decides
> efficiently — including high-degree polynomial identities
> bit-blasting cannot encode and DSP datapath equivalences where
> overflow cancellation makes the polynomials non-zero but the
> functions identical. We give a decision procedure based on
> strong Gröbner bases over $\mathbb{Z}_{2^d}$ for polynomial
> ideal membership, and a vanishing polynomial test using falling
> factorials for function equivalence. The two procedures
> together solve 18 random polynomial identities at degree
> ${\geq} 18$ that no bit-blasting configuration can encode within
> 10 s, and 5 DSP datapath equivalences where cvc5 takes 180×
> longer. Both are implemented in CBMC and proven sound in
> Lean 4 (25 theorems, 0 sorry); the formalisation effort
> identified and removed a 2000× ordering sensitivity in the
> C++ implementation.**

This commits to:
- Specific benchmark wins, not "competitive on".
- Specific competitors (bit-blasting cannot encode; cvc5 180×
  slower on `dsp_horner_16`).
- Specific gain from formalisation, not a vague "we proved it
  sound".

### The ideal-membership-vs-function-equivalence distinction

Paper 2 currently muddles two separate semantic claims:

| Claim | Object | Procedure | Completeness |
|---|---|---|---|
| C1 | Polynomial $f$ is in ideal $\langle g_1, \ldots, g_k \rangle$ over $\mathbb{Z}_{2^d}$ | Strong Gröbner basis | Complete for ideal membership |
| C2 | Polynomial $f - g$ vanishes as a function on $\mathbb{Z}_{2^{n_1}} \times \cdots \to \mathbb{Z}_{2^m}$ | Vanishing polynomial test | Complete for function equivalence |

C2 is strictly stronger than C1 over $\mathbb{Z}_{2^d}$ because
some polynomials (e.g. $4x^2 + 4x \pmod 8$) are non-zero in the
ideal-membership sense but vanish as functions. This gap is the
*reason* C2 exists, and it is the most important conceptual
contribution.

Currently the paper introduces C1 in §2, then in §4 says "the
solver is incomplete: it returns inconclusive when the basis
contains only even constants". That framing makes C2 sound like
remediation. The truth is that C1 and C2 decide *two different
problems*; the verification engineer cares about C2 (functional
equivalence), and we provide a decision procedure for it. C1 is a
component used to build that, but C2 is the headline.

## Four-classes taxonomy as the organising scaffold (R3)

The taxonomy in §1 is currently:

> universal × equational (commutativity), existential ×
> equational (factoring), universal × relational (bounds checking),
> existential × relational (overflow detection).

Currently this is mentioned and never reused. The mapping to our
techniques is precise and useful:

| Class                   | Example                          | Algebraic procedure | Bit-blasting (Paper 1) |
|---|---|---|---|
| Universal × equational  | $\forall a, b. \, ab = ba$       | **Decides** (Gröbner / vanishing) | Slow but decides |
| Existential × equational SAT-direction (witness) | $\exists x. \, p(x) = c$ | Falls through | Decides; sometimes very slow |
| Existential × equational UNSAT-direction (no witness) | $\neg \exists x. \, p(x) = c$ | Refutes via Rabinowitsch | Decides |
| Universal × relational  | $\forall a. \, |a \cdot b| < 2^{30}$ | Falls through | **Decides** (Paper 1's combacs target) |
| Existential × relational | overflow exists witness | Falls through | **Decides** (Paper 1's combacs target) |

This gives Paper 2 a *clear scope statement*: we contribute on the
top two rows; Paper 1 contributes on the bottom three. The two
papers are *complementary by construction*, not "complementary in
some informal sense".

### How the taxonomy threads through the paper

**§1 (Introduction).**
- Replace the current four-classes paragraph with the table above.
- State the scope: "this paper addresses the universal-equational
  class and the UNSAT direction of existential-equational; the
  bit-blasting companion paper addresses the universal-relational
  and existential-relational classes more uniformly".
- The contribution sentence becomes: "we give a *decision
  procedure* (not just a heuristic) for the universal-equational
  class, complete in two senses: ideal membership over
  $\mathbb{Z}_{2^d}$ (Gröbner) and function equivalence (vanishing
  polynomial)".

**§3 (Algebraic Solving via Gröbner Bases).**
- §3.0 frames the section as "the first half of our coverage of
  the universal-equational class: ideal membership".
- §3.3 ("Contributions Beyond Song et al.") lists the
  three axes; renaming the third axis from "Mechanised Soundness"
  to "Formalisation-Driven Refinement" lifts the Lean → C++
  feedback story (R4).

**§4 (Vanishing Polynomial Test).**
- §4.0 frames the section as "the second half: extending ideal
  membership to function equivalence over $\mathbb{Z}_{2^d}$".
- The current "the solver is incomplete" opening flips: instead
  of "the Gröbner solver is incomplete and we patch it", say
  "ideal membership is the wrong question for SMT — function
  equivalence is — so we give a separate procedure that decides
  the right question".
- The current §4.4 ("Why a separate test, instead of adding
  vanishing polynomials to the Gröbner basis?") becomes the
  natural follow-up: we tried it the unified way and it fails for
  reasons we can articulate. Currently buried; should be
  promoted.

**§7 (Evaluation).**
- §7.5 (Random Polynomial Identity Suite, 210 benchmarks) is the
  strongest result; should be promoted from "the fifth
  sub-evaluation" to either §7.1 or its own section.
- The category breakdown in §7.5 ("addition", "multiplication",
  "correctness", "equality", "nonequality", "bounding",
  "identity-point", "root-finding") maps directly onto the
  taxonomy:

| Category              | Class                                          | Win pattern         |
|---|---|---|
| addition              | universal × equational                         | Algebraic dominates |
| multiplication        | universal × equational                         | Algebraic dominates |
| correctness           | universal × equational                         | Algebraic dominates |
| equality (SAT)        | existential × equational SAT-direction         | Bit-blasting dominates |
| nonequality (SAT)     | existential × equational SAT-direction         | Bit-blasting dominates |
| bounding              | universal × relational                         | Tied                |
| identity-point        | universal × equational (special instance)      | Tied                |
| root-finding          | existential × equational SAT-direction         | Bit-blasting dominates |

Reorganise §7.5 with this column visible. The taxonomy then
*explains* the win pattern rather than narrating it
empirically.

**§9 (Related Work).**

The current §9 has 7 paragraphs that overlap. Reorganise around
the taxonomy:

- **Universal × equational, ideal membership.** Song et al. 2024
  (foundational), Bryant 1991 (BDD lower bounds), Clegg et al.
  1996 (Gröbner > resolution).
- **Universal × equational, function equivalence.**
  Shekhar et al. 2007 (vanishing ideal characterisation),
  Gámez-Montolio et al. 2024 (efficient normalisation, our
  Algorithm 3 source).
- **Universal × equational on gate-level circuits.** Biere,
  Kauers, Ritirc 2017 (gate-level Gröbner), Kaufmann thesis
  2020, Kaufmann–Biere Amulet2 2021, Yu et al. 2016
  (function extraction).
- **Existential × equational and finite-field generalisations.**
  Özdemir cvc5 ff option 2023 (prime fields), Howe et al. 2025
  (subpolynomial decomposition).
- **Word-level rewriting (covers all four classes uniformly).**
  Niemetz et al. 2023 Bitwuzla; cvc5's QF\_BV pipeline.
- **Relational classes (where Paper 1 contributes).**
  Companion citation; explicit cross-reference.
- **Proof complexity.** Buss 1995 extended Frege.

This makes §9 about half its current length without dropping any
citation. The class-by-class structure also makes it easy for the
reader to see which work occupies which corner of the design
space.

**§10 (Conclusion / Future Work).**
- Reframe "Towards a true theory solver" as
  "Extending to relational classes via bit-decomposition
  variables" — directly using the taxonomy to motivate the
  open direction.
- Move the *introduction* of bit-decomposition variables from
  the conclusion to a §3.4 forward-pointer (R9), keeping the
  conclusion descriptive.

## Section-by-section concrete plan (R1–R10 instantiated)

### Abstract (rewrite, ~22 lines → ~16 lines)

Current opening: "We present algebraic techniques…"

Replacement (sketch):

> Verifying high-degree polynomial identities and DSP datapath
> equivalences in bit-vector SMT exposes a gap that current
> word-level rewriting and bit-blasting cannot bridge: an
> identity over $\mathbb{Z}_{2^d}$ that becomes a
> non-zero-but-vanishing polynomial under overflow, or a
> degree-$\geq 18$ polynomial whose bit-blasted multiplication
> exceeds practical SAT capacity.
>
> We give a decision procedure for the universal-equational
> fragment of QF\_BV, with two components. (1) A strong
> Gröbner-basis solver over $\mathbb{Z}_{2^d}$ deciding ideal
> membership in $\sim 2$ ms regardless of bitwidth, with
> progress-based termination derived from the Lean 4 termination
> proof. (2) A vanishing polynomial test using falling
> factorials and Stirling numbers, deciding function equivalence
> over $\mathbb{Z}_{2^{n_1}} \times \cdots \to \mathbb{Z}_{2^m}$
> in microseconds. On a 210-benchmark random polynomial suite
> the procedure solves 18 instances at degree $\geq 18$ that no
> bit-blasting configuration can encode within 10 s; on 5 DSP
> datapath benchmarks it is up to 180× faster than cvc5. We
> match Bitwuzla's word-level rewriting on simple identities and
> match the bit-blasting baseline on a 66-benchmark SMT-COMP
> stratified sample. Soundness is mechanised in Lean 4 (25
> theorems, 0 sorry, including a Mathlib contribution under
> review).

This commits to specific wins (18 instances at degree $\geq 18$;
180× vs cvc5 on `dsp_horner_16`) and explicitly scopes via the
class ("universal-equational fragment"). The "match Bitwuzla on
simple, match bit-blasting on community" framing is a *floor*
result rather than the headline.

### §1 (Introduction)

- Drop the commutativity-at-BW=16 hook. It establishes
  bit-blasting fails, but Bitwuzla already wins this round
  syntactically. A weak hook for an algebraic paper.
- Lead with the gap: "polynomial identities at degree $\geq 18$
  are uniformly hard for bit-blasting (cannot even encode
  within 10 s); DSP datapath equivalences where the difference
  polynomial is non-zero but vanishes as a function are uniformly
  hard for both bit-blasting and word-level rewriting (cvc5 takes
  180× longer than us on `dsp_horner_16`)".
- Insert the four-classes table (R3) explicitly, with our scope
  highlighted.
- Three contributions, not two:
  1. Decision procedure for universal-equational ideal membership
     (strong Gröbner basis over $\mathbb{Z}_{2^d}$, progress
     termination, end-to-end SMT integration).
  2. Decision procedure for universal-equational function
     equivalence (vanishing polynomial test via falling
     factorials and Kronecker products).
  3. Mechanised soundness in Lean 4, where the formalisation
     effort directly improved the C++ implementation
     (eliminating a 2000× ordering sensitivity).

### §2 (Algebraic Solving via Gröbner Bases)

- Add a one-paragraph framing: "This section gives the
  ideal-membership half of our universal-equational decision
  procedure. Section 3 gives the function-equivalence half."
- §2.2 (progress-based termination): the Lean-feedback paragraph
  ("the need to prove termination in Lean forced us to isolate
  the 'progress' notion …") should be lifted to a named
  paragraph header, or a sidebar, or a sub-subsection. It is
  currently buried.
- §2.3 (Contributions Beyond Song et al.): rename third axis from
  "Mechanised Soundness" to "Formalisation-Driven Refinement",
  with the 2000× story as the punch line.

### §3 (Vanishing Polynomial Test) — promote, reframe

- Open with: "Ideal membership in $\mathbb{Z}_{2^d}$ is not the
  right question for SMT. Function equivalence is. We give a
  separate decision procedure for it — complete, in milliseconds,
  using falling factorials and Stirling numbers."
- §3.0 should contain a one-paragraph contrast:
  $4x^2 + 4x \pmod 8$ is non-zero in the ideal but vanishes as a
  function. Verification engineers care about the latter.
- §3.4 ("Why a separate test, instead of adding vanishing
  polynomials to the basis?") is currently a great section
  buried at depth 3. Promote to §3.5 sub-subsection or move to
  §3.0 immediately after the framing — the reader should see
  *why we made this design choice* before the algorithmic
  details.
- §3.5 (worked example $4x^2 + 4x$) is good, keep.
- §3.6 (overflow encoding worked example) is good, keep.
- §3.7 (commutativity Gröbner worked example) is good, keep —
  but it belongs in §2, not §3 (it's a Gröbner example, not a
  vanishing one).

### §7 (Evaluation) — major reorganisation

Current order:
1. Custom suite (39)
2. SMT-COMP (66)
3. SMT-LIB community (26)
4. Amulet2 comparison
5. Random polynomial suite (210)  ← strongest result
6. Threats to validity

Proposed order:
1. **Random polynomial suite (210)** — promoted to §7.1.
   Restructured by taxonomy class. The 18 algebraic-only wins
   become the headline table.
2. **DSP datapath equivalence (5)** — promoted from a paragraph
   in §7.1 to its own §7.2. The vanishing polynomial test's win
   condition; cvc5 takes 1.84 s, we take 10 ms.
3. **Custom suite (39)** — demoted to §7.3, with a forward
   pointer "we designed this suite during development, see §7.1
   and §7.2 for results on benchmarks we did not design".
4. **SMT-COMP community sample (66)** — §7.4, framed as "the
   negative-control": on broader QF\_BV we are neither faster
   nor slower than the bit-blasting baseline, confirming our
   techniques are pattern-specific, not general.
5. **SMT-LIB community (26)** — §7.5, similar framing.
6. **Amulet2 comparison** — §7.6, re-scoped: the comparison is
   not a head-to-head, it's a *complementarity* statement.
7. **Threats to validity** — §7.7, re-scoped via taxonomy.

### §8 (Mechanised Soundness Proofs)

Currently 20 lines. Either:
- (a) Expand to 40–50 lines with the Lean → C++ feedback
  story as the punch line, OR
- (b) Cut to 10 lines and merge into §2.3 as the third axis.

Option (b) is preferable for length reasons, with the punch line
"the formalisation revealed a 2000× ordering bug, which we
reported and fixed in the C++ implementation" lifted to §2.3.

### §9 (Related Work) — reorganise by taxonomy class

See the seven-bucket structure under "How the taxonomy threads
through the paper" above. This shrinks §9 from 7 paragraphs to
6, removes overlap, and gives the reader a structural reason for
the ordering.

### §10 (Conclusion)

- Drop "Towards a true theory solver" as new content; move
  expression-level normalisation and bit-decomposition variables
  to §3.4 ("Future Directions Within the Universal-Equational
  Class") and §10 contains only a 2-paragraph summary.
- The summary should hit: scope (universal-equational), result
  (decided in milliseconds, including the 18 algebraic-only
  wins), open direction (relational classes via
  bit-decomposition).

## Hedging language pass (R8)

The phrase "complementary" appears 6 times; "fast path" 3 times;
"matching mature reasoners" 2 times; "competitive on simple
identities" once. Standardise:

- **"Complementary"**: keep only in the explicit cross-reference
  to Paper 1 (one instance). Elsewhere, replace with the specific
  scope statement (e.g., "this paper addresses the universal-
  equational class").
- **"Fast path"**: drop entirely. We are not a fast path; we are
  a decision procedure.
- **"Matching mature reasoners"**: state the actual
  result — Bitwuzla's word-level rewriting is roughly 30%
  faster than us on commutativity microbenchmarks, but neither
  Bitwuzla nor cvc5 has the 18 high-degree polynomial-identity
  wins we report. The reader should learn what we lose, what we
  win, and why.
- **"Competitive on simple identities"**: drop. Either we win
  or we lose; faint praise serves neither.

## Risks and things to preserve

### Risks

1. **Over-claiming.** The 18 algebraic-only wins are real but
   they are on a *random* polynomial suite that we did not
   design. The benchmarks at degree $\geq 18$ are intentionally
   chosen to be hard for bit-blasting. We should not claim
   "decides degree $\geq 18$ in general" but rather "decides
   the random-polynomial benchmarks at degree $\geq 18$ that
   our suite includes". Brain et al. 2025 own the suite design;
   we cite and report.
2. **Too aggressive scope statement.** "Decision procedure for
   universal-equational" is technically accurate over the
   polynomial fragment but the SMT logic includes shifts,
   bitwise operations, etc.\ that fall outside. State scope
   precisely: "decision procedure for the polynomial fragment
   of QF\_BV's universal-equational queries".
3. **Reorganisation breaks anchors / cross-references.** The
   current paper has many `\ref{}` to specific sections; check
   each before / after.

### Things to preserve

- **The bitwidth-independence story.** Current §3.4 has the
  Bitwuzla / cvc5 / shift-add scaling table at BW=8 to 256.
  Bitwuzla is faster than us on this microbenchmark; we should
  retain the table but reframe as "validation that the procedure
  does not blow up with bitwidth", not "we are competitive with
  Bitwuzla". Bitwidth-independence is a property; the contest
  with Bitwuzla is decided elsewhere (DSP, random polynomial).
- **The honest threats-to-validity section.** Section 7.6 names
  the bias in our custom suite explicitly. Keep this; the
  taxonomy reorganisation makes the bias narrower (we win on
  the universal-equational class, not on QF\_BV in general).
- **The Lean PR #38628 unit-characterisation contribution.**
  Currently mentioned only briefly. The Mathlib contribution is
  external evidence that the formalisation work is independently
  valuable. Keep, perhaps with a one-line citation.
- **The Amulet2 comparison's scope-not-time framing.** Currently
  honest; the rewrite should preserve the framing while
  clarifying that we are *not* claiming a head-to-head win.
- **The non-anonymisation deferral.** Per user, anonymisation is
  not yet the active concern. The rewrite plan stays content-
  focused; an anonymisation pass happens after the structural
  rewrite is stable.

## Sequenced task list

Tasks ordered by dependency. R1, R2, R3 are intertwined; R4–R10
can be applied in any order once R1–R3 land.

| Order | Task | Effort | Notes |
|---|---|---|---|
| 1 | R1: re-write abstract + §1 introduction | 4 h | Anchors the rest of the rewrite |
| 2 | R3: insert four-classes table in §1 with our scope highlighted | 1 h | Shared with R1 |
| 3 | R2: ideal-membership-vs-function-equivalence framing in §2.0 + §3.0 | 2 h | |
| 4 | R5: reframe §3 (vanishing) opening; promote §3.4 ("why a separate test") | 2 h | |
| 5 | R4: lift Lean → C++ feedback in §2.2 + §2.3 | 1 h | |
| 6 | R6: reorganise §7 in the proposed order | 3 h | Requires care with table refs |
| 7 | R7: rewrite §9 by taxonomy class | 2 h | |
| 8 | R9: move "Towards a true theory solver" content to §3.4 forward pointer | 30 min | |
| 9 | R10: tighten §1 (re-evaluate hook after R1) | 1 h | |
| 10 | R8: hedging language pass | 1 h | Run after content is stable |
| 11 | Verification: full PDF compile, ref check, ToC scan | 1 h | |

Total: ~18.5 hours. Should fit in 2–3 days of focused editing.

## Decision points for the user / co-authors

1. **Headline win.** Recommend "18 algebraic-only wins on random
   polynomial suite at degree $\geq 18$". Alternative: "DSP
   datapath equivalence with vanishing polynomial test, 180×
   faster than cvc5". Both are strong; prefer the random
   polynomial because it is on a benchmark suite we did not
   design.
2. **Scope statement.** Recommend "polynomial fragment of
   QF\_BV's universal-equational queries". Alternative
   formulations on request.
3. **Conclusion's vision.** Currently the conclusion sketches
   bit-decomposition variables as a future direction. Should
   this stay in the conclusion or move to a §3.4
   future-directions subsection within scope?
4. **Length budget.** Current 24 pages. The reorganisation
   should not add length; some sections shrink (§9, §8) and
   others grow (§7.1 random polynomial promotion). Net should
   be neutral or -1 page. TACAS LNCS limit is 16 pages + 4
   appendix; we are over by 4–8 already. The rewrite is *not*
   the moment to address length — that's a separate pass.

## What this plan does *not* do

- Does not add experiments or benchmarks.
- Does not change the technical claims; it changes which claims
  are foregrounded.
- Does not address anonymisation (deferred).
- Does not address LNCS length compliance (deferred until after
  the structural rewrite is stable).
- Does not change the Lean development.
- Does not change the C++ implementation.

## Process for applying the plan

1. Create a working branch (e.g. `paper-2-restructure-2026-05`).
2. Apply tasks 1–11 in order. After each task, compile the PDF
   and check the diff.
3. After all tasks: re-read end-to-front. Compare against this
   plan; flag any regressions to the diagnosis above.
4. Have the user review before merging to `features/adder`.

This is the plan. No edits to `paper.tex` yet; awaiting approval.
