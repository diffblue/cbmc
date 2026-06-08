# Rewrite Plan: SPJ Principles Analysis

Brutal, honest assessment of `paper.tex` against Simon Peyton Jones's paper-writing principles. Section-by-section.

---

## Overall Diagnosis

The paper has strong technical content and real results. The introduction is already good—it opens with a concrete example (SPJ principle #2) and states refutable contributions. But the paper suffers from three systemic problems:

1. **Two papers crammed into one.** The Gröbner basis solver and comba-cs are independent contributions with independent evaluations. The paper tries to serve both and ends up with a diffuse "one ping" (SPJ #1). The title says "Algebraic and Encoding Optimizations"—that's two things.

2. **Description-list disease.** The paper uses `\begin{description}` as a crutch in Background, Cross-Solver Analysis, and Negative Results. These read as bullet-point dumps, not flowing narrative. SPJ #6 says use visual structure, but description lists are not visual structure—they're lazy structure.

3. **The evaluation is a wall of tables.** Seven tables in the evaluation section, many without narrative that tells the reader *what to learn* from each one. Tables should support claims; here, claims sometimes support tables.

**The one ping should be:** *Carry propagation—not circuit size—is the hardness source for multiplication in SAT, and encodings that separate carry propagation from column reduction dramatically outperform those that don't.* The Gröbner basis solver is a bonus layer, not the main insight. Reframe accordingly.

---

## Section-by-Section Analysis

### Title

**Current:** "Algebraic and Encoding Optimizations for Arithmetic in SAT-Based Verification"

**Problem:** Generic. "Optimizations" is vague. Two topics joined by "and" signals a diffuse paper. Violates SPJ #1 (one ping).

**Suggestion:** Lead with the insight, not the technique list.

> "Carry Propagation Is the Enemy: Encoding Multiplication for SAT-Based Verification"

or more conservatively:

> "Carry-Save Encoding and Algebraic Solving for Multiplication in Bounded Model Checking"

### Abstract

**What works:** Concrete numbers (2.6–71×, 31,000×). Comparison against Bitwuzla and cvc5. The "33 vs 31 vs 28" framing is punchy.

**Problems:**
- "four-layer approach" is mentioned but never explained in the abstract. The reader has no idea what the four layers are. Either name them or drop the framing.
- "691 existing regression tests" is an implementation detail, not an abstract-worthy claim.
- The abstract buries the insight. It leads with the Gröbner basis (the less novel contribution—Song et al. 2024 already did this) instead of the carry-propagation insight.

**Rewrite suggestion:**
> Multiplication is a bottleneck in SAT-based bounded model checking: the standard shift-and-add encoding creates carry chains that cause exponential blowup in solver effort. We show that carry propagation—not circuit size—is the dominant hardness source: at 13 bits, integer multiplication needs 23× more conflicts than carry-free GF(2) multiplication despite only 1.6× more clauses. Based on this insight, we present comba-cs, a carry-save Comba encoding that separates column reduction from carry propagation, achieving 2.6–71× speedup across four SAT solvers. For pure polynomial equations (commutativity, associativity, overflow), a Gröbner basis solver over Z_{2^d} resolves them algebraically in under 1 ms regardless of bitwidth. On 36 QF_BV benchmarks, CBMC solves 33 instances—more than Bitwuzla (31) and cvc5 (28).

This leads with the insight, not the mechanism.

### Introduction (Section 1)

**What works well:**
- Opens with a concrete example (SPJ #2). This is excellent—exactly what SPJ recommends.
- The example escalates nicely: shift-add times out → comba-cs solves in 5.3s → Gröbner solves in 0.009s.
- Contributions are enumerated and forward-referenced (SPJ #9).
- Active voice throughout.

**Problems:**

1. **Contribution #2 (carry propagation as hardness source) should be contribution #1.** It's the intellectual core of the paper—the *insight*. The encoding is the *application* of the insight. Currently the insight is buried as contribution #2 behind the encoding, which is backwards. SPJ #8: the most important claim should come first.

2. **Contribution #5 (negative results) is not a contribution.** "We tried 20 things that didn't work" is not a refutable claim (SPJ #8). It's useful content, but listing it as a contribution inflates the contribution count and dilutes the real ones. Cut it from the numbered list; mention it in prose: "Section N catalogues approaches that failed, to save future effort."

3. **Five contributions is too many.** SPJ recommends 3–4 sharp claims. Merge #1 and #3 (the encoding and the adaptive heuristic are one system), keep #2 (the insight), keep #4 (Gröbner). That's three.

4. **"poorly understood" is vague.** The sentence "the interaction between encoding choices and modern SAT solver techniques... is poorly understood" is a gap statement, but it doesn't say *what* is poorly understood. Be specific: "No prior work has systematically evaluated how multiplier encodings interact with inprocessing BVE and congruence closure across multiple solvers."

5. **The paragraph starting "We present a layered approach" is slightly redundant** with the contribution list that follows. Tighten: go straight from the problem to the contributions.

**Rewrite suggestion for contribution list:**

> Our contributions are:
>
> 1. **Carry propagation as the hardness source.** We compare integer and GF(2) multiplication and show that carry propagation—not circuit size—causes exponential blowup in SAT solver effort (Section 3).
>
> 2. **Carry-save Comba encoding (comba-cs).** Based on this insight, we separate column reduction from carry propagation, achieving 2.6–71× speedup. An adaptive heuristic selects the encoding per multiplication, eliminating regressions (Section 4).
>
> 3. **Algebraic solving via Gröbner bases.** A strong Gröbner basis computation over Z_{2^d} solves polynomial equations in under 1 ms regardless of bitwidth, with soundness verified by 25 mechanized theorems in Lean 4 (Section 5).
>
> Section 6 catalogues 20+ approaches that failed, including Karatsuba, Toom-Cook, and XOR Gaussian elimination.

### Background (Section 2)

**This is the weakest section of the paper.** It reads as a textbook dump—exactly what SPJ warns against.

**Problems:**

1. **Description-list format for encodings.** Four encoding descriptions (shift-add, Dadda, Wallace, Comba) presented as a glossary. The reader doesn't know *why* they need to know this yet. SPJ #4: put the reader first. Introduce encodings *when they're needed*, not in a background dump.

2. **Description-list format for SAT techniques.** BVE, inprocessing, glue/LBD, congruence closure—another glossary. The reader doesn't know which of these matter yet.

3. **The propagation completeness subsection** (2.2) is good—it motivates the approach. But it's buried after two glossary subsections.

4. **Wallace trees are never mentioned again.** If it's not used in the paper, cut it from background.

**Structural suggestion:** Cut this section entirely. Fold the necessary definitions into the sections that use them:
- Move encoding descriptions into Section 4 (comba-cs), where the reader needs to understand what comba-cs improves upon.
- Move BVE/inprocessing into Section 3 (hardness) or Section 4, where BVE interaction is discussed.
- Move propagation completeness into Section 4 as motivation.
- Move congruence closure into the cross-solver analysis where it's actually relevant.

If you must keep a Background section, make it one paragraph: "CBMC encodes N-bit multiplication by accumulating N partial products into a 2N-bit result. The encoding choice determines how this accumulation is performed. We compare four encodings (shift-add, Dadda, Comba, and our comba-cs) in Section 4." Then move on.

### Carry Propagation Hardness (Section 3)

**What works well:**
- Clean experimental design: integer vs. GF(2) is an elegant isolation of the carry-propagation variable.
- Table 1 is small and focused.
- The "23× more conflicts despite only 1.6× more clauses" is a memorable, quotable result.
- Honest about it being empirical evidence, not a formal proof.

**Problems:**

1. **The BVE-completeness threshold paragraph** at the end is jarring. It introduces a new concept (106% BVE elimination) that isn't set up. The reader doesn't know what BVE is yet if you've cut Background. Move this to Section 4 where the adaptive heuristic is discussed—it's the *reason* for the adaptive heuristic.

2. **"This is consistent with known exponential resolution lower bounds"**—passive voice, and the connection to Haken is hand-wavy. Be precise: Haken proved exponential resolution lower bounds for the pigeonhole principle; the connection to multiplication carry chains is by analogy, not by reduction. Say so.

3. **Missing narrative arc.** The section presents data but doesn't tell the reader what to *do* with the insight. Add a bridge sentence: "This motivates an encoding that minimizes carry propagation depth—which is exactly what comba-cs does."

**Minor:** "We note this is empirical evidence, not a formal proof" reads as a disclaimer. Rewrite as active: "We emphasize that this is empirical evidence; a formal proof of exponential resolution complexity for multiplication remains open."

### Carry-Save Comba Encoding (Section 4)

**What works well:**
- The two-pass description is clear and concise.
- The counterintuitive result (2× more clauses but 30× faster) is well-highlighted.
- DRAT proof analysis (Table 2) provides mechanistic evidence.
- The adaptive heuristic is well-motivated.

**Problems:**

1. **The adaptive heuristic subsection mixes policy and mechanism.** The pre-scan implementation detail ("runs in `boolbvt::set_to()`") is irrelevant to the paper's audience. Cut implementation details; keep the decision logic.

2. **"The popcount's internal additions use ripple-carry regardless of the top-level adder encoding, preventing the Brent-Kung adder from being used inside the popcount (see Appendix A)."** This sentence is an implementation footnote masquerading as a paragraph. Move to appendix or cut.

3. **The sparse-constant fallback paragraph** is another implementation detail. One sentence is enough: "For constant multiplication with few partial products, comba-cs falls back to Dadda-style reduction."

4. **Table 2 (DRAT proof comparison) needs narrative.** Currently: table, then one sentence. Expand: what do the numbers *mean*? "The 74% increase in fixed variables means comba-cs enables the solver to determine more variable values through unit propagation alone, reducing the search space."

### Four-Solver Evaluation (Section 5)

**This section has too many subsections (7) and too many tables (7).** The reader drowns in data. SPJ #6: visual structure should guide, not overwhelm.

**Problems:**

1. **Seven subsections is too many for one evaluation section.** Merge aggressively:
   - Merge "Multiplier Encoding Comparison" and "Cross-Solver Analysis" into one subsection: "Encoding × Solver Interaction."
   - Merge "Industrial Benchmarks" and "SMT-LIB QF_BV Benchmarks" into one subsection: "Benchmark Results."
   - "Scaling" can be a paragraph within the encoding comparison, not its own subsection.
   - "Algebraic Solving via Gröbner Bases" should be its own *section*, not a subsection of evaluation. It's a separate contribution.
   - "External Solver Comparison" can stay.
   - "Threats to Validity" can stay but should be shorter.

2. **The Gröbner basis subsection (5.6) is misplaced.** It's a major contribution buried as evaluation subsection 5.6. Promote it to its own section (Section 5), and make the current evaluation Section 6. This also fixes the structural problem of having the Gröbner basis *contribution* described in the *evaluation* section rather than having its own methods section.

3. **Table 3 (all encodings × all solvers) is too large.** 14 rows × 6 columns. The reader's eyes glaze over. Options:
   - Split into two tables: one for commutativity (the main story), one for matrix trace (the exception).
   - Or: keep only the rows that illustrate the key points and move the rest to an appendix.

4. **Cross-Solver Analysis uses description lists again.** Four solver descriptions as `\item[CaDiCaL (71×):]`. This should be flowing prose with a table or figure. Consider a bar chart showing speedup per solver—that's the visual structure SPJ recommends.

5. **Table 5 (industrial benchmarks) has a regression (keyed hash 0.2×) that's explained away in prose.** Good that it's honest, but the explanation is buried. Highlight it: "The one regression (keyed hash, 1.3s → 6.5s) occurs because..."

6. **Table 6 (QF_BV benchmarks) mixes three different stories** (comba-cs wins, matched, regression) in one table. The "Matched" rows add nothing—they show 1.0× speedup. Cut them or move to appendix.

7. **"Threats to Validity" is boilerplate.** "Our benchmarks are custom-created" and "may not represent all real-world verification workloads" is obvious. Be specific about what *could* invalidate the results: "The main threat is benchmark selection bias: our benchmarks emphasize multiplication-heavy verification, which is common in cryptography and DSP but rare in typical pointer-safety checking."

8. **Passive voice creeps in:** "All experiments were run on..." → "We ran all experiments on..."

### Negative Results (Section 6)

**What works well:**
- Reporting negative results is genuinely valuable.
- The Karatsuba/Toom-Cook/Schönhage-Strassen table is informative.
- The opening paragraph connecting subquadratic algorithms to the hardness insight is good.

**Problems:**

1. **Description-list dump again.** Two subsections, each a description list. This reads as a lab notebook, not a paper section. SPJ #4: tell a story.

2. **No narrative arc.** The section is organized by "things that hurt" and "things with limited benefit." Better organization: group by *why* they failed, connecting back to the carry-propagation insight.

   Suggested structure:
   - **Paragraph 1:** Subquadratic algorithms fail because their combination steps reintroduce carry chains (connects to Section 3).
   - **Paragraph 2:** Approaches that add structure (radix-4, AND caching, full-adder popcount) fail because they add carry chains.
   - **Paragraph 3:** Approaches that exploit XOR structure (Gaussian elimination, CryptoMiniSat XOR) fail because CBMC's XOR gates are too short.
   - **Paragraph 4:** Solver tuning and abstraction refinement fail because the problem is structural, not parametric.

3. **"A significant portion of this investigation produced negative results"** is throat-clearing. Cut it. Start with: "A natural first question is whether asymptotically superior algorithms..."—which is already the next sentence.

4. **Some items are too terse.** "AND gate caching between multiplications: 89% slower. Sharing partial product variables prevents independent BVE." This needs one more sentence explaining *why* sharing prevents BVE.

5. **Some items are too detailed for a negative-results section.** The CaDiCaL option tuning (512 combinations) is interesting but could be one sentence: "Tuning 16 CaDiCaL options across 4 encodings and 8 benchmarks produced no improvement exceeding ±3%."

### Related Work (Section 7)

**What works well:**
- Comprehensive coverage.
- Credits prior work warmly (SPJ #5): "Kaufmann extended this," "Song et al. go further."
- Explains how each work relates to ours.
- The Jia et al. paragraph is excellent—it explains what they did, what we tested, and why results differ.

**Problems:**

1. **Too long and dense.** At ~40 lines, this is a wall of text. Break into thematic paragraphs with clear topic sentences. Currently it's one long section with no visual breaks.

2. **The paragraph structure is chronological, not thematic.** SPJ recommends organizing related work by *relationship to your work*, not by publication date. Suggested grouping:
   - **Algebraic/polynomial methods** (Bryant, Biere/Kauers/Ritirc, Kaufmann, Yu, Mahzoon, Song)—these are closest to our Gröbner basis work.
   - **Encoding and SAT techniques** (Eén/Biere, Brain, Tseitin/Plaisted, Fazekas, Jia)—these are closest to our comba-cs work.
   - **Word-level solvers** (Niemetz/Bitwuzla, cvc5)—these are our comparison targets.
   - **Circuit verification** (Chukharev)—complementary.

3. **Some citations are drive-by.** "Encoding techniques for SAT have been studied extensively [Tseitin, Plaisted]" is a throwaway sentence. Either explain how Tseitin/Plaisted relate to your encoding choices or cut the citation.

4. **Missing comparison with Kaufmann's domain choice.** You note "their approach works over Q with field polynomials x²−x=0... ours works directly over Z_{2^d}." But you don't say *why* Z_{2^d} is better (or whether it is). Is it faster? Simpler? More natural for BMC? This is exactly the kind of comparison SPJ wants—generous but clear about differences.

### Conclusion (Section 8)

**Problem: It repeats the abstract.** Almost verbatim. SPJ #10 explicitly warns against this.

**What a conclusion should do:**
1. Restate the *insight* (not the results) in one sentence.
2. State what changed in practice (comba-cs is now the default in CBMC).
3. State open problems and future work.

**Current conclusion has no future work** despite the section title saying "Conclusion and Future Work." The only forward-looking content is implicit (the Gröbner basis is incomplete for non-polynomial problems).

**Rewrite suggestion:**

> Carry propagation—not circuit size—is the dominant source of hardness for multiplication in SAT-based verification. Comba-cs exploits this by separating column reduction from carry propagation, achieving 2.6–71× speedup on commutativity benchmarks. For polynomial equations, a Gröbner basis solver eliminates SAT encoding entirely. Both techniques are now defaults in CBMC.
>
> Several directions remain open. First, the Gröbner basis solver is incomplete for non-polynomial constraints (bitwise operations, inequalities); extending it with theory combination could close this gap. Second, the adaptive heuristic uses a simple multiplication count; a more sophisticated analysis of formula structure (e.g., detecting symmetry between multiplier circuits) could improve encoding selection. Third, our carry-propagation hardness result is empirical; a formal proof of exponential resolution complexity for multiplication would place this on firmer theoretical ground.

### Appendices

**Appendix A (Adder Encoding Interaction):** This is fine as an appendix. It's detailed and specialized. One issue: the "g-only BVE Catalyst" subsection is important enough that it should be mentioned (briefly) in the main text, not just relegated to the appendix. The g-only technique is part of the default configuration.

**Appendix B (BVE Interaction):** Good content, appropriate for appendix. The non-monotonic hint effect is fascinating and worth keeping.

**Threshold Sensitivity (A.3):** This is pure appendix material. Fine where it is.

---

## Cross-Cutting Issues

### Passive Voice

The paper is mostly active voice (good!), but passive creeps in:

- "All experiments were run on..." → "We ran all experiments on..."
- "Benchmarks comprise 37 verification problems" → "We evaluate on 37 verification problems in 5 categories"
- "This is because: (1) division's internal multiplication always uses shift-add" → "This happens because division's internal multiplication always uses shift-add"
- "The soundness of the Gröbner basis solver is verified by 25 mechanized theorems" → "We verified soundness with 25 mechanized theorems"

Do a full passive-voice sweep.

### Description Lists as Crutch

Six description lists in the paper:
1. Background §2: encoding descriptions
2. Background §2.1: SAT solver techniques
3. Evaluation §5.2: cross-solver analysis
4. Negative Results §6.1: approaches that hurt
5. Negative Results §6.2: approaches with limited benefit
6. (Implicit) Adaptive heuristic enumeration

Convert all to flowing prose. Description lists are appropriate for API documentation, not for a research paper narrative.

### Figures

**The paper has zero figures.** This is a major SPJ #6 violation. Tables are not figures. Suggestions:

1. **Figure 1: The comba-cs two-pass diagram.** Show a partial product grid, the first pass (column reduction), the carry collection, and the second pass. This is the core contribution—it deserves a picture.

2. **Figure 2: Scaling plot.** Table 4 (scaling) should be a line plot: bitwidth on x-axis, time on y-axis, two lines (std. Comba vs. comba-cs). The visual would immediately show the diverging curves.

3. **Figure 3: The four-layer architecture.** A simple block diagram showing: source → word-level simplification → Gröbner basis → comba-cs/shift-add → SAT solver. This replaces the "four-layer" prose description.

4. **Optional Figure 4: Speedup bar chart.** Cross-solver speedup comparison as a grouped bar chart instead of the description-list prose.

### Redundancy

Several results are stated three times (abstract, introduction, evaluation). The "33 vs 31 vs 28" comparison appears in the abstract, end of introduction, Table 8, and conclusion. State it once prominently (evaluation), reference it from abstract and conclusion.

### Section Ordering

**Current:** Introduction → Background → Hardness → Comba-cs → Evaluation (with Gröbner buried inside) → Negative Results → Related Work → Conclusion

**Suggested:**

1. Introduction
2. Carry Propagation Hardness (the insight—put it first, SPJ #1)
3. Carry-Save Comba Encoding (the application of the insight)
4. Algebraic Solving via Gröbner Bases (promoted from eval subsection)
5. Evaluation (all empirical results, including external comparison)
6. Negative Results (shortened, narrative form)
7. Related Work
8. Conclusion and Future Work

This puts the insight before the technique (SPJ #2), gives the Gröbner basis its own section, and separates methods from evaluation.

---

## Priority Ranking

If you can only do five things:

1. **Promote Gröbner basis to its own section.** It's a contribution, not an evaluation subsection.
2. **Add 2–3 figures.** The partial-product grid diagram and scaling plot are essential.
3. **Kill the description lists.** Convert all six to flowing prose.
4. **Reorder contributions** so the insight (carry propagation hardness) comes first.
5. **Rewrite the conclusion** with actual future work instead of abstract repetition.

If you can do five more:

6. Cut or radically shorten Background (fold into later sections).
7. Merge evaluation subsections (7 → 4).
8. Rewrite Negative Results as narrative grouped by failure mode.
9. Reorganize Related Work thematically.
10. Full passive-voice sweep.
