# Master Task List

## Context

Three sources of input:
1. **Martin Brain** — encoding ideas, problem taxonomy, paper structure
2. **German reviewer** — methodology as contribution (DRAT→insight→encoding loop), AI's role, token cost
3. **review-summary.md** — GenAI feedback loop literature survey, positioning our work

Key decision: **Two papers**, not one.

---

## Paper 1: Bit-Blasting Encodings for Multiplication in SAT

**Focus:** The encoding side — comba-cs, the multiplier zoo, negative results,
and the DRAT-proof-driven methodology that led to the encoding design.

### Content (from existing work)
- [ ] Carry propagation hardness analysis (GF(2) comparison)
- [ ] comba-cs encoding design and evaluation
- [ ] Adaptive heuristic
- [ ] Four-solver evaluation (CaDiCaL, MiniSat, MergeSat, CryptoMiniSat)
- [ ] Negative results (Karatsuba, Toom-Cook, Schönhage-Strassen, radix-4/8, etc.)
- [ ] g-only BVE catalyst
- [ ] BVE interaction analysis
- [ ] DRAT proof analysis (bottleneck variables, clause lifecycle)

### New content needed
- [ ] **Methodology section: DRAT→insight→encoding feedback loop**
  - Frame as a scientific method: analyze proof traces, identify bottlenecks,
    redesign encoding, measure improvement
  - This is the "highlight" the German reviewer wants
  - Position as a manual instance of the GenAI feedback loop pattern
  - Cite the related work from review-summary.md (AutoSAT, SATformer, etc.)
  - Note: no existing work closes the full loop (proof trace → encoding redesign)
  - Discuss potential for automation (future work)

- [ ] **Token/effort analysis**
  - How many tokens/iterations did the AI-assisted development take?
  - What was the human's role vs the AI's role?
  - Could this methodology be transferred to other encoding problems?

- [ ] **Booth encoding** (from Martin's list of "harder but wouldn't it be nice")
  - Implement Booth-encoded multiplier in CBMC
  - Evaluate against comba-cs and shift-add
  - Booth reduces partial products by half but adds complexity

- [ ] **Encoding #1: 4-bit block multiplication** (Martin's idea)
  - Divide inputs into 4-bit sections
  - Use optimal 4×4→8 propagation-complete sub-multiplier (Brain et al. 2016)
  - Sum diagonals, organize into non-overlapping words
  - Implement and evaluate

- [ ] **Encoding #2: Sorting network based** (Martin's idea)
  - Compute n² partial product bits
  - Sort each diagonal with bitwise sorting network ((x|y, x&y))
  - Add auxiliary sorted-property constraints
  - Extract carries by ANDing neighbors
  - Merge-sort carries with next diagonal
  - Implement and evaluate

- [ ] **Multiple encodings simultaneously** (Martin's "mad idea")
  - Encode same multiplication two ways on same variables
  - Solver uses whichever propagates better
  - Evaluate overhead vs benefit

- [ ] **Division and remainder**
  - Note applicability: a = b*q + r with non-deterministic q, r
  - Same encoding techniques apply to the internal multiplier

- [ ] **Problem taxonomy** (from Martin)
  - Universal/equational (∀x,y. P(x,y) = Q(x,y)) vs existential (∃x,y. P(x,y) = c)
  - Bit-blasting for existential, algebraic for universal
  - Explain why both are needed

- [ ] **QF_BV benchmark caveat** (from Martin)
  - Some QF_BV benchmarks are circuit-equivalence problems
  - These are encoding-sensitive and can make evaluations misleading
  - Discuss how to handle this in evaluation

### Evaluation needed
- [ ] Implement Booth encoding and benchmark
- [ ] Implement 4-bit block encoding and benchmark
- [ ] Implement sorting network encoding and benchmark
- [ ] Run on existing benchmark suite + QF_BV community benchmarks
- [ ] Measure token count for the AI-assisted development process

---

## Paper 2: Algebraic Approaches to Bit-Vector Arithmetic

**Focus:** Gröbner basis, vanishing polynomials, normalization, and the
algebraic layer of the five-layer architecture.

### Content (from existing work)
- [ ] Strong Gröbner basis over Z_{2^d}
- [ ] Rabinowitsch trick for disequalities
- [ ] Vanishing polynomial test (Shekhar/Kalla + Gàmez-Montolio Algorithm 3)
- [ ] Word-level simplification
- [ ] Lean 4 mechanized proofs (25 theorems)
- [ ] Equation ordering insight (2000× impact)
- [ ] Fresh variable decomposition for inline expressions
- [ ] Candidate extraction + SAT hints

### New content needed
- [ ] **Comparison with CoCoALib** (cvc5's finite field solver uses it)
  - How does our implementation compare?
  - What does CoCoALib provide that we don't?
  - Could we use CoCoALib instead of our custom implementation?

- [ ] **Connection to Kaufmann/Biere's gate-level work**
  - Their approach: gate polynomials + field polynomials over Q
  - Our approach: word-level polynomials over Z_{2^d}
  - Formal comparison: when does each approach apply?
  - The boolean constraint gap (our investigation showed 2-bit works, 4-bit doesn't)

- [ ] **Kalla's work in depth** (Shekhar et al. 2007)
  - We implemented their algorithm — provide detailed comparison
  - Our contribution: integration into BMC, SSA substitution, zero_extend handling

- [ ] **Arnau's normalization** (BAR 2024)
  - We implemented Algorithm 3 — provide detailed comparison
  - Stirling number approach vs brute-force
  - Performance on DSP benchmarks

- [ ] **Post-quantum crypto application** (Martin's SABER reference)
  - Polynomial multiplication in rings (NTT-based)
  - Could our techniques verify SABER implementations?

- [ ] **Scaling analysis**
  - Algebraic: scales with bitwidth, not variables
  - Bit-blasting: scales with variables, not bitwidth
  - Formal complexity comparison

### Evaluation needed
- [ ] Compare against CoCoALib on polynomial benchmarks
- [ ] Create SABER-inspired benchmarks (polynomial ring multiplication)
- [ ] Scaling experiments: vary bitwidth and variable count independently
- [ ] Measure Gröbner basis step count vs polynomial degree/variables

---

## Cross-Cutting Tasks

### Paper logistics
- [ ] Decide venues for both papers (PoS 2026? FMCAD? CAV? SMT workshop?)
- [ ] Author list finalization
- [ ] Split existing paper.tex into two paper drafts
- [ ] Ensure no self-plagiarism between the two papers

### Implementation
- [ ] Run git-clang-format on all changed files
- [ ] Full 691 CORE regression test pass (verified, pre-existing failures only)
- [ ] Consider upstreaming to CBMC develop branch

### Lean 4 / Mathlib
- [ ] Submit the ZMod PR (branch ready at tautschnig/mathlib4)
- [ ] Monitor Gröbner basis PR #29203 in Mathlib

### The "GenAI methodology" angle
- [ ] Document the DRAT→insight→encoding methodology explicitly
- [ ] Quantify: how many DRAT analyses led to encoding changes?
- [ ] Quantify: token count for the full development process
- [ ] Frame as "manual FunSearch for SAT encodings"
- [ ] Identify what structured solver output would enable automation
  (cf. "AI Coding Agents Need Better Compiler Remarks")
- [ ] This could be a third paper or a section in Paper 1

---

## Priority Order

**Immediate (this week):**
1. Split paper.tex into two drafts (Paper 1 and Paper 2)
2. Write the methodology section for Paper 1 (DRAT feedback loop)
3. Implement Booth encoding (Martin's request, straightforward)

**Short-term (next 2 weeks):**
4. Implement 4-bit block encoding (Martin's Encoding #1)
5. Implement sorting network encoding (Martin's Encoding #2)
6. Benchmark all new encodings
7. Write up algebraic paper (Paper 2) — mostly reorganizing existing content

**Medium-term (next month):**
8. Token count analysis for the GenAI methodology angle
9. CoCoALib comparison
10. SABER benchmarks
11. Submit both papers

**Deferred:**
12. Multiple-encodings-simultaneously experiment
13. Automated DRAT→encoding feedback loop (future work / third paper)
14. Mathlib PR follow-up

---

## Status Update (2026-05-06)

### Completed since last update:
- [x] Paper 1 written (14 pages, 33 references)
- [x] Paper 2 first draft (6 pages, 11 references)
- [x] Mathlib PR feedback addressed (iff version, pushed)
- [x] Martin's taxonomy added to both papers
- [x] Booth encoding fixed and benchmarked
- [x] Full solver statistics analysis (conflicts, propagations, BVE, fixed, proof size)
- [x] Learned clause / proof compactness analysis

### Paper 2 expansion items (open):
- [ ] More detail on Gröbner basis algorithm (currently just the existing section from combined paper)
- [ ] Equation ordering insight (definitions before Rabinowitsch = 2000× impact)
- [ ] Fresh variable decomposition for inline expressions (smt2_solver path)
- [ ] Scaling analysis: demonstrate bitwidth independence formally (BW=8,16,32,64 same time)
- [ ] Comparison with Kaufmann/Biere (Q + field polynomials vs Z_{2^d})
- [ ] The boolean constraint gap (x²-x=0 enables 2-bit but not 4-bit hw_mul_equiv)
- [ ] More DSP benchmark detail (describe each benchmark, what makes it hard)
- [ ] Candidate extraction + SAT hints (Level 3 architecture)
- [ ] Progress-based Buchberger termination (from formal proof insight)

### Other open items:
- [ ] Token/effort analysis for GenAI methodology (Paper 1)
- [ ] Self-plagiarism check between the two papers
- [ ] CoCoALib comparison (Paper 2 future work or experiment)
- [ ] SABER-inspired benchmarks (Paper 2 future work)

---

## Senior Review Findings (2026-05-06)

Performed a thorough review of both papers. Key findings in doc/senior-review.md.

### Paper 1 — Critical issues that MUST be fixed

- [ ] **The "methodology contribution" claim is overstated.** We did NOT use
      DRAT analysis to DESIGN Booth/block4/sortnet — those are pre-existing
      encodings we implemented. Rewrite Section 4 to distinguish the
      discovery process (retrospective) from the methodology (prescriptive).
      Concretely describe WHICH variable was identified as bottleneck,
      HOW it was traced back to encoding structure.
- [ ] **Internal contradictions:** Text references truncated/broken ("15 benchmarks",
      "1728 = 36 benchmarks × 4 multiplier encodings ×", phantom sec:bve).
      Need full proofread pass to fix.
- [ ] **Causation vs correlation:** The GF(2) claim shows correlation not
      causation. Address this head-on or weaken the claim.
- [ ] **The bf16 paradox:** Identical clause counts across encodings
      contradicts the narrative. Explicitly acknowledge and explain.
- [ ] **Attribution:** block4 was Martin Brain's idea from BAR 2024. Must
      credit him explicitly.
- [ ] **Weak evidence for "17× faster", "2× faster":** Single-benchmark claims.
      Need more benchmarks per claim OR explicit scoping.
- [ ] **Missing: variance/statistical significance.**
      Currently median of 3 runs; need 10+ runs and stddev reported.
- [ ] **Missing: adaptive heuristic ablation.**
      What if we disable the pre-scan? What if we always use popcount?
- [ ] **Writing issues:** repetition (31% bottleneck in 3 places), bloated
      abstract, unremoved algebraic fragments in Related Work.

### Paper 2 — Critical issues that MUST be fixed

- [ ] **Too short at 6 pages.** Need to expand to 10-14 pages.
- [ ] **Missing theory:** doesn't define "strong Gröbner basis", gives no
      pseudocode, claims complexity without derivation.
- [ ] **Missing example walk-throughs:**
      - Buchberger step-by-step on a simple benchmark
      - Stirling number conversion example
      - S-polynomial reduction example
- [ ] **Unjustified 2000× speedup claim:**
      Experiment running (ordering ablation).
- [ ] **Novelty over Song et al. unclear:**
      Need to clearly delineate which algorithmic contributions are ours.
- [ ] **Five-layer table confusing:**
      What is cbmc vs smt2 column? Why 0s? Why 0.0s? Clarify.
- [ ] **DSP benchmarks are custom — major methodological weakness.**
      Need to supplement with standard benchmarks.
- [ ] **Community benchmark results BURIED in subsection**
      — and actually show Bitwuzla beats us (7 vs 6).
      Must surface honestly.
- [ ] **Missing: comparison with cvc5's CoCoALib-based finite field solver.**
- [ ] **Missing: scaling experiments.**
      Experiment running (bitwidth 8→256).
- [ ] **Missing: Kaufmann/Biere connection developed in depth.**
      Currently just one paragraph.
- [ ] **Missing: "boolean constraint gap" finding** from our investigation
      (2-bit works, 4-bit doesn't).

### Cross-cutting issues

- [ ] **Benchmarks are mostly custom** — both papers need more standard
      benchmarks (SMT-COMP QF_BV, ISCAS multipliers, SV-COMP programs).
- [ ] **No five-layer ablation** — what does 1/2/3/4/5 layers solve?
      Experiment running.
- [ ] **"Companion paper" citations are informal** — need formal
      cross-references once venues decided.
- [ ] **Authors say "TBD"** — placeholder needs resolution.
- [ ] **GenAI methodology thread underdeveloped:**
      - Token/effort count not measured
      - Iteration count not tracked
      - Concrete AI→human→encoding example not shown
      - Transferability claim unsubstantiated

### Background experiments (started in parallel)

1. **Bitwidth scaling** (PID 1881): comm/assoc at BW=8,16,32,64,128,256
2. **Equation ordering ablation** (PID 4134): normal vs reverse on 6 benchmarks × 3 runs
3. **Layer ablation** (PID 4732): 5 configurations × 12 benchmarks

### Additional experiments needed

- [ ] **Statistical significance**: re-run key benchmarks 10+ times, report mean±stddev
- [ ] **SMT-COMP benchmarks**: download subset of SMT-COMP QF_BV, evaluate all encodings
- [ ] **ISCAS multiplier equivalence**: standard hardware benchmarks
- [ ] **SV-COMP**: program verification benchmarks with multiplication
- [ ] **Polynomial degree scaling**: Gröbner basis time vs degree
- [ ] **Number of variables scaling**: Gröbner basis time vs #vars
- [ ] **Proof size across all encodings × all benchmarks** (not just strength_chain_16)
- [ ] **comm_256, comm_512 to demonstrate bitwidth-independence clearly**
