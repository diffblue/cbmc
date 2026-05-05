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
