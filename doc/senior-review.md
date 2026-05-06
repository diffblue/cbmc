# Senior Review of Papers 1 and 2

Brutally honest assessment as a senior researcher would give a junior author.

## Paper 1: "Proof-Guided SAT Encoding Selection for Multiplication in BMC"

### Strengths
- Clear narrative arc: methodology → hardness source → comba-cs → alternatives → evaluation
- Strong opening example (T/O → 5.3s for one encoding change)
- Honest about limitations and negative results
- Good visual structure (TikZ diagram, scaling plot)

### Critical issues — MUST fix before submission

**1. The "methodology contribution" claim is overstated and poorly supported.**

The paper claims the proof-guided methodology is "the primary contribution," but the methodology section (Section 4) is only ~50 lines and describes the process *retrospectively* with a single concrete datapoint (31% bottleneck variable).

- We have NO evidence that this methodology is transferable. Claiming "applied to alternative encodings" is false — we did NOT apply DRAT proof analysis to invent Booth/block4/sortnet. Those are pre-existing encodings we implemented and benchmarked. The paper conflates "I ran DRAT analysis on existing encodings" with "I used DRAT analysis to DESIGN encodings."
- The "31% bottleneck" finding needs more detail: WHICH variable? How was it identified? What did the trace look like? What's the reproducible procedure?
- The "AI automation" paragraph at the end of Section 4 is speculative and doesn't belong in a contribution claim.

**2. Internal contradictions and broken references.**

Looking at the paper:
- Section 7 (Evaluation) references `Table~\ref{tab:allencodings}` but the table has mixed encoding data
- Line "This is exactly what \combacs does." appears twice (end of Section 3 AND implied in Section 5)
- The text "identities (commutativity, overflow, strength reduction: 15 benchmarks" is truncated/broken
- "where 1728 = 36 benchmarks × 4 multiplier encodings ×" also truncated
- Section 9 references "the algebraic solver" (from Paper 2) without explaining — awkward

**3. The carry propagation claim is still empirical only.**

Section 3 acknowledges this but then the abstract says "we show that carry propagation—not circuit size—is the dominant hardness source." We show correlation, not causation. A reviewer would push back: maybe XOR structure is what helps, not reduced carry depth.

**4. The comba-cs data (Section 5) claims 31% bottleneck variable but evaluation shows identical clause counts on bf16.**

The identical formula finding (explained in Section 9's subsection about bf16) contradicts the narrative of Section 4 (where comba-cs is designed to reduce bottlenecks). If comba-cs produces IDENTICAL clauses to shift-add on bf16, how can its bottleneck analysis be generalizable?

**5. The Alternative Encodings section (6) is weak.**

- Booth: we spent effort fixing bugs; this isn't novel — it's a textbook encoding applied to SAT. What's our contribution? Just the observation that it wins on constant mul?
- block4: Martin Brain's idea (BAR 2024). We implemented it. We need to be more honest — "Martin Brain suggested this idea in BAR 2024 and we implemented/evaluated it."
- sortnet: negative result, OK.

The "No Single Encoding Dominates" subsection is a good framing but the claim isn't well-supported — we don't have enough benchmarks per problem class.

**6. Claims that need more evidence.**

- "17× faster on constant multiplication" — ONE benchmark (strength_chain_16). Need more.
- "2× faster on commutativity" — tested only commutativity at BW=16 via FP path, which is suspicious given identical formulas for other encodings.
- Proof size claims (277KB vs 10MB) — only one benchmark.

**7. Missing essentials for a scientific paper.**

- No discussion of STATISTICAL SIGNIFICANCE. Every measurement is a median of 3 runs — but we don't report variance.
- No ABLATION for the adaptive heuristic components.
- No discussion of what happens on larger bitwidths (32, 64).
- The evaluation tables use a mix of solvers (CaDiCaL, MiniSat, MergeSat, CryptoMiniSat) inconsistently.
- No clear statement of EXPERIMENTAL METHODOLOGY (machine setup appears but is buried).

**8. Writing issues.**

- Repetition: the "31% bottleneck" appears in Sections 1, 4, and 5.
- Abstract is 220 words; could be tightened.
- Section 9 (Related Work) has remnants of algebraic content that weren't fully removed.
- The closing sentence of Section 4 ("No existing work automates this full cycle") is overclaiming — we didn't do a systematic literature review.

## Paper 2: "Algebraic Solving for Bit-Vector Arithmetic in BMC"

### Strengths
- Nice opening (ab - ba = 0 as polynomial identity)
- Clear separation of Gröbner basis vs vanishing polynomial test
- Has Lean 4 proofs (strong credibility booster)
- Specific headline number (41/44 beats Bitwuzla)

### Critical issues — MUST fix before submission

**1. Paper is too SHORT at 6 pages.**

For a venue like SMT 2026, FMCAD, or TACAS, 6 pages is incomplete. Strong workshop papers are typically 8-12 pages; strong conference papers 12-16. The paper feels incomplete because:
- Only 1 proof sketch theorem
- The Gröbner basis section is dense but not expansive
- Vanishing polynomial test: algorithm described in 4 bullet points
- No examples walk-through
- Related work is thin (3 short paragraphs)

**2. Missing theory and algorithm details.**

The Gröbner basis section:
- Does NOT define "strong Gröbner basis" (vs. standard)
- Does NOT give the algorithm (no pseudocode)
- The "2000× speedup from equation ordering" is claimed but never shown
- No discussion of how Buchberger termination interacts with the 100K step limit

The vanishing polynomial section:
- Stirling numbers of the second kind are mentioned but not defined
- The Kronecker product approach is not illustrated with a small example
- Complexity claim $O(d_w^{2k})$ is stated without derivation

**3. Claims about Gröbner basis novelty are unclear.**

Paper 2 says "5 contributions beyond Song et al." but doesn't compare them clearly:
- Which parts are OUR work vs. Song et al.'s?
- Song et al. 2024 already showed strong Gröbner bases solve the equational theory; what's truly new?
- "2000× speedup from equation ordering" — is this a reproducible engineering insight or is it specific to our implementation?

**4. The five-layer table (Table 1 in Section 3) is confusing.**

The table shows two columns: `cbmc` and `smt2`. What is the difference? Reader has no idea without reading other sources. Why are some cells "—"? Some show 0s (not 0.0s).

**5. Evaluation is thin.**

- 44 benchmarks total, 8 of which we designed ourselves (the DSP ones).
- DSP benchmarks are DESIGNED BY US to showcase our technique — this is a major methodological weakness.
- The comparison with Bitwuzla/cvc5 is on these custom benchmarks.
- The 26 SMT-LIB community benchmarks are hidden in a subsection; results reversed (Bitwuzla 7, CBMC 6).

**6. Missing experiments a reviewer will demand.**

- Performance vs. bitwidth: claim bitwidth-independence but only show 1ms at BW=16 and BW=32. Need BW=8, 16, 32, 64, 128, 256, 512.
- Performance vs. number of variables: scales with variables — what's the curve?
- Polynomial degree scaling: Gröbner basis degree vs. time.
- Large-scale benchmark on SMT-LIB QF_BV (not just 26 benchmarks).
- Comparison with cvc5's CoCoALib-based finite field solver.

**7. The "equation ordering insight" is folklore without proof.**

Section 2 claims "equation ordering strategy (definitions before Rabinowitsch) that improves performance by 2000×" — this is a striking number but has NO experiment section showing it. A reviewer will ask: prove it.

**8. Writing issues.**

- Section 3 mentions a "five-layer" architecture but Paper 2 only describes 2 layers (Gröbner + vanishing). The five-layer table includes comba-cs/shift-add from Paper 1 — cross-paper dependency that's awkward.
- Related Work mentions Kaufmann/Biere's connection but doesn't develop it.
- The "boolean constraint gap" finding (2-bit works, 4-bit doesn't) from our investigation is NOT in the paper.
- The SABER/post-quantum angle is mentioned in future work but not explored.

## Combined Review

### Problems spanning both papers

**1. Self-referencing is broken.**

- Paper 1 refers to "a companion paper" (Paper 2) but without citation.
- Paper 2 shows a "five-layer" table that includes comba-cs from Paper 1.
- The papers cross-reference but neither citation is concrete.

**2. Benchmarks are custom — this is a methodological red flag.**

Both papers rely heavily on benchmarks WE designed. Any reviewer will demand:
- SMT-COMP benchmarks (QF_BV division)
- Hardware verification benchmarks (ISCAS, multiplier equivalence)
- Program verification benchmarks from SV-COMP

**3. No ablation of the "five-layer" system.**

The claim is that 5 layers achieve 41/44. What does 4, 3, 2, 1 layer(s) achieve? This isn't shown.

**4. Author ambiguity.**

Both papers list "Michael Tautschnig" and "TBD." The "TBD" is a placeholder that needs resolution.

**5. The GenAI methodology thread is underdeveloped.**

The German reviewer asked us to make the DRAT→insight→encoding loop a scientific highlight, and quantify AI's contribution. Neither paper:
- Measures token/effort count for AI assistance.
- Quantifies HOW MANY iterations the AI-human loop took.
- Shows a concrete example of AI-identified bottleneck → human-validated encoding change.
- Demonstrates the transferability claim.

### What a reviewer will reject on

**Paper 1 (currently):** "The methodology contribution is not substantiated beyond one datapoint. The alternative encodings section is a catalog of textbook encodings with limited novelty. The carry propagation hardness claim isn't causally established. Reject."

**Paper 2 (currently):** "Too short; insufficient theory; evaluation on custom benchmarks. The Gröbner basis contribution over Song et al. isn't clearly delineated. The vanishing polynomial test implementation is of existing algorithms. Weak reject."

## What to do next

### Tier 1: Paper 1 — Must do
1. Rewrite methodology section with CONCRETE procedure + multiple examples
2. Remove internal contradictions and broken references
3. Add variance/statistical analysis
4. Expand Alternative Encodings — honestly attribute block4 to Martin Brain
5. Fix the bf16 paradox narrative
6. Add ablation study of adaptive heuristic

### Tier 1: Paper 2 — Must do
1. Expand to 10-14 pages with proper theory
2. Add example walk-throughs (Buchberger step-by-step, Stirling conversion)
3. Prove the 2000× equation ordering claim
4. Add scaling experiments (bitwidth 8→512)
5. Clarify novelty vs Song et al.
6. Reduce reliance on custom DSP benchmarks

### Tier 2: Both papers
1. Get MORE benchmarks (SMT-COMP, ISCAS, SV-COMP)
2. Ablation studies
3. Statistical significance
4. Formalize the GenAI methodology story
5. Resolve authorship

### Experiments we should run in the background
1. **Scaling experiment** for Gröbner basis: bitwidth 8, 16, 32, 64, 128, 256 on comm/assoc/distrib
2. **Equation ordering ablation**: run WITH and WITHOUT "definitions before Rabinowitsch" to verify 2000× claim
3. **Layer ablation**: run with 1/2/3/4/5 layers enabled, measure solved count
4. **Extended benchmarks**: SMT-COMP QF_BV subset, ISCAS multiplier equivalence
5. **Proof size measurements** across all encoding×benchmark pairs (not just 1)
6. **Variance measurement**: 10+ runs instead of 3
