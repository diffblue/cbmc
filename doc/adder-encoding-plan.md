# Adder Encoding: Next Steps Plan

## Context

We evaluated 7 adder encodings across 5 benchmarks and 2 SAT solvers.
Key finding: no single encoding dominates. The Rani MUX encoding is
7.6x faster than the PC default on the hard subtract benchmark (MiniSat),
but slower on others. See `doc/adder-encoding-evaluation.md` for full data.

## Phase 1: Expand the evidence base

1. Run on real-world benchmarks (SV-COMP, AWS C Commons, CBMC regression
   suite). Adapt `scripts/profile_cbmc.py --auto` to measure solver time.

2. Test with more solvers (Kissat, Glucose). If CaDiCaL's insensitivity
   holds for other modern solvers, encoding choice matters mainly for MiniSat.

3. Check whether the 04_subtract pattern (subtraction-heavy, SAT) occurs
   in real verification tasks.

## Phase 2: Understand WHY the differences exist

4. **Dump and analyze proof traces.** Use MiniSat's and CaDiCaL's proof
   logging to compare conflicts, learned clause sizes, and propagation
   counts between PC_ripple and Rani_MUX on 04_subtract.

   Key question: **are there clauses that are always learned?** If the
   solver consistently discovers the same lemmas across runs, we could
   provide those clauses upfront as redundant clauses in the encoding.
   This would avoid the solver having to rediscover them via conflict
   analysis, potentially giving the speedup of a better encoding without
   changing the encoding itself.

   Approach:
   - Build MiniSat/CaDiCaL from sources in `build/` with proof logging
   - Generate DIMACS for 04_subtract with both PC and Rani encodings
   - Run solver, collect learned clauses
   - Intersect learned clauses across multiple runs (different random seeds)
   - Identify "universal lemmas" that appear in every run
   - Check whether these lemmas correspond to carry-chain properties
     (e.g., generate-skip, group propagate) that could be added to the
     encoding

5. Analyze the interaction with preprocessing. Check whether MiniSat
   with SatELite preprocessing closes the gap with CaDiCaL.

6. Check whether Rani MUX is "accidentally" propagation complete for
   subtraction specifically (a + NOT(b) + 1 has carry_in=1 and one
   inverted operand, which may make the MUX encoding effectively PC).

## Phase 3: Implement the improvement

Based on Phase 1-2 findings, one of:

**Path A: Solver-aware encoding selection**
- Runtime check in `bv_utilst::adder()` selects encoding based on solver
- Add `--adder-encoding {pc,mux,lookahead,auto}` command-line option

**Path B: Universal lemma injection**
- If Phase 2 step 4 identifies consistent learned clauses, add them as
  redundant clauses in the encoding (like the generate-skip idea, but
  data-driven rather than hand-crafted)

**Path C: Hybrid encoding**
- Refine generate-skip clauses, apply selectively

## Phase 4: Clean up the PR

- Remove parallel prefix adders (uniformly worse, 300+ lines dead code)
- Keep Rani MUX and carry lookahead as alternatives behind CLI option
- Update evaluation document with real-world results
- Add correctness regression tests for each encoding

## Phase 5: Upstream and validate

- Full CI suite with each candidate encoding
- Performance benchmarking CI (`profiling.yaml`)
- Submit PR with evaluation, implementation, and results

## Phase 2 Results: Proof Trace Analysis

### Experiment: Universal Learned Clauses

On the equivalence-check benchmark (N=100, UNSAT, ~35K vars, ~125K clauses),
we ran CaDiCaL 3 times with different random seeds and collected the learned
binary clauses from each run's DRAT proof.

**Finding: 10,336 binary clauses are learned in ALL runs regardless of seed.**

These "universal lemmas" are structural consequences of the adder encoding
that the solver must always discover. They represent implications between
carry-chain variables that are not directly encoded but are always needed
for the proof.

### Impact of Pre-Providing Universal Lemmas

Adding these 10,336 binary clauses to the original CNF (8% clause overhead):

| Configuration | CaDiCaL time |
|---------------|-------------|
| Original | 7.82s |
| + universal binary lemmas | **4.33s** |
| **Speedup** | **1.81x (45%)** |

### Implications

This confirms the hypothesis: there are clauses that the solver always
needs to learn, and providing them upfront avoids redundant work. The
next step is to identify WHAT these clauses represent structurally
(likely carry-chain implications) and generate them directly in the
encoding rather than mining them from proof traces.

If these universal lemmas correspond to the generate-skip or propagate-skip
patterns we identified earlier, this provides a principled justification
for adding those redundant clauses to the encoding.

### Deeper Analysis: What Do Universal Lemmas Represent?

**Tiny equivalence check (1 addition pair):**
- 201 universal binary clauses
- Dominant pattern: c2→c1 (49 clauses) — carry of adder 2 implies
  carry of adder 1
- These are INTER-ADDER implications arising from the equality
  constraint `sum1 == sum2`
- No single-adder encoding change can provide these

**Large equivalence check (N=100):**
- 10,336 universal binary clauses
- 7,140 within-iteration (inter-adder carry implications)
- 3,196 cross-iteration (assertion framework)
- Adding them gives 45% speedup (7.82s → 4.33s CaDiCaL)

**Single-adder UNSAT (N=200):**
- 4,299 universal binary clauses
- **0 within-iteration** — ALL are cross-iteration
- These are about loop iteration relationships, not adder encoding
- Adding them gives 34% speedup (5.62s → 3.69s CaDiCaL)

### Key Insight

**The universal lemmas are NOT about the adder encoding.** They are
about higher-level problem structure:
- Inter-adder carry relationships (for multi-adder formulas)
- Cross-iteration relationships (for loop-based formulas)

This means:
1. **Improving the adder encoding cannot provide these lemmas.**
   The encoding determines per-addition solving difficulty, but the
   lemmas the solver needs are about relationships between additions.

2. **The 45% speedup from lemma injection is real but requires
   problem-specific analysis** — we can't generate these lemmas
   from the encoding alone.

3. **For improving the adder encoding itself**, the focus should be
   on minimizing per-addition solving cost (clause count, BCP
   efficiency) rather than trying to capture cross-adder relationships.

### Revised Recommendation

The adder encoding research should focus on:
1. **Clause count minimization** — the Rani MUX encoding's advantage
   on hard benchmarks comes from having fewer clauses
2. **BCP efficiency** — the MUX carry creates 2-literal implications
   that are faster for BCP than the PC encoding's 3-literal clauses
3. **The PC encoding remains the best default** for its robustness,
   but the Rani MUX should be available as an option

The universal lemma injection is a separate optimization opportunity
that could be implemented as a preprocessing step, independent of
the adder encoding choice.
