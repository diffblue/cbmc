# Review Response Plan

## Immediate fixes (writing only)

### M1. Qualify the "33 vs 31" claim
- Add "on our custom benchmark suite" every time the claim appears
- Locations: abstract, end of introduction, external comparison section
- Effort: 10 minutes

### m1. Table 3 too large
- Move MiniSat and CryptoMiniSat rows to appendix, keep CaDiCaL and MergeSat in main text
- Or: split into commutativity table + matrix trace table
- Effort: 15 minutes

### m2. Explain "106% BVE elimination"
- Add: "through resolution, BVE creates new variables that are themselves eliminated in subsequent rounds, so the cumulative elimination count can exceed the original variable count"
- Effort: 5 minutes

### m3. Fix proof sketch (conflates soundness/completeness)
- Remove case (2) from the proof sketch — it's about completeness, not soundness
- Rewrite to focus only on: odd constant → unit → 1 ∈ I → I = R → no solution
- Effort: 10 minutes

### m4. Fix "~O(n³)" notation
- Change to "grows roughly as n³ (measured across BW=5–17)"
- Effort: 2 minutes

### m6. Fix 37 vs 36 inconsistency
- Check: is there a 37th benchmark? If so, name it. If not, fix to 36.
- Effort: 5 minutes (need to check benchmark data)

### m7. Split Related Work into thematic subsections
- Algebraic/polynomial methods (Bryant, Clegg, Biere/Kauers, Kaufmann, Yu, Mahzoon, Song)
- Encoding and SAT techniques (Eén/Biere, Brain, Jia, Fazekas, Tseitin/Plaisted)
- Word-level and complementary (Niemetz/Bitwuzla, Chukharev)
- Effort: 20 minutes

### m9. Fix double "the"
- "because the the carry-save" → "because the carry-save"
- Effort: 1 minute

### m10. Clarify AI authorship vs declaration
- Remove "TBD" as co-author, keep Declaration on Generative AI
- Or: clarify in declaration that Kiro is a tool, not an author
- Decision needed from Michael
- Effort: 5 minutes

## Requires collecting data from prior experiments

### m5. Explain the 1728-benchmark suite
- These are 36 benchmarks × 48 configurations (4 encodings × 4 solvers × 3 adder encodings)
- Need to verify this. Check bench-multiplication/smt2-results-v7-clean.tsv
- Add one sentence explaining the composition
- Effort: 10 minutes

### m6 (continued). Check 37 vs 36
- Check the actual benchmark list
- Effort: 5 minutes

### Q2. Adaptive heuristic threshold sensitivity
- We have threshold sensitivity data in Appendix (Table in Threshold Sensitivity section)
- But that's about PP sparsity and width thresholds, not the multiplication count threshold
- Need to check: what happens with threshold=3 or threshold=4?
- May need a quick experiment
- Effort: 30 minutes if experiment needed

### Q3. Step limit behavior
- Check: do any benchmarks hit the 100K step limit?
- The progress-based termination means most terminate early
- Need to report what happens when step limit is reached (returns UNKNOWN, falls through to SAT)
- Effort: 10 minutes to verify from prior data

## Requires new experiments

### M1 (strengthened). SMT-LIB community benchmarks (Q1)
- Run CBMC's smt2_solver on a subset of SMT-LIB QF_BV benchmarks
- Even 50-100 benchmarks from the SMT-LIB repository would help
- This is the strongest way to address the external validity concern
- Effort: 2-4 hours (download benchmarks, run, analyze)
- PRIORITY: HIGH — this is the most impactful improvement

### M3. Better isolation of carry propagation
- The reviewer wants a comparison where ONLY carry propagation depth differs
- Idea: compare ripple-carry accumulation vs. carry-lookahead accumulation
  of the SAME partial products (both integer, same circuit, different carry depth)
- We already have this data: shift-add (long carry chains) vs Dadda (short carry chains)
  with the same partial products. The Dadda vs shift-add comparison IS this experiment.
- May just need to reframe the argument rather than run new experiments
- Effort: 30 minutes to rewrite the argument

## Requires new content

### M2. Clarify novelty over Song et al.
- List what is new: (1) integration into BMC tool, (2) Rabinowitsch trick for
  disequalities (Song et al. handle equations only), (3) fresh variable decomposition
  for inline expressions, (4) candidate extraction + SAT hints (Level 3),
  (5) Lean 4 mechanization, (6) equation ordering insight (2000× impact)
- Add a paragraph explicitly distinguishing our contribution
- Effort: 20 minutes

### M4. Add figures (TikZ)
- Figure 1: comba-cs two-pass diagram (partial product grid → column reduction → carry collection → carry reduction)
- Figure 2: Scaling plot (BW on x-axis, time on y-axis, two lines)
- Effort: 1-2 hours for TikZ diagrams

### m8. Enumerate Lean 4 theorems
- Add a brief enumeration to the Gröbner basis section or appendix
- Group by: (a) Z_{2^d} unit characterization, (b) ideal preservation,
  (c) Rabinowitsch soundness, (d) Buchberger termination
- Effort: 15 minutes

### Q4. Gröbner basis as standalone decision procedure
- Answer: yes, for the polynomial fragment. But the polynomial fragment
  is a strict subset of QF_BV (no bitwise ops, no inequalities, no shifts).
- Add one sentence to the Gröbner basis section
- Effort: 5 minutes

## Priority order

1. **M1 + Q1**: Qualify claims + run SMT-LIB benchmarks (highest impact)
2. **M4**: Add TikZ figures (biggest visual improvement)
3. **M2**: Clarify Gröbner novelty over Song et al.
4. **M3**: Reframe carry propagation argument
5. **m3**: Fix proof sketch
6. All other minor fixes (m1, m2, m4, m5, m6, m7, m8, m9, m10, Q2-Q4)
