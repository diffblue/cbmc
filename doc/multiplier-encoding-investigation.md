# Multiplier Encoding Investigation

## Objective

Apply the deep SAT solver analysis techniques developed in the adder
encoding investigation (see `doc/adder-encoding-investigation.md`) to
understand and improve CBMC's multiplication encoding. The adder
investigation revealed that encoding structure profoundly affects
CaDiCaL's performance through mechanisms like BCP cascade depth
(glue-1 learned clauses), BVE polarity alignment, and SAT/UNSAT
asymmetry. This investigation applies the same analytical framework
to multiplication.

## Starting Point

The branch `tautschnig/feature/multiplier-encoding` contains:
- Multiple encoding implementations: baseline (shift-add), Dadda tree,
  Wallace tree, Comba (popcount-based), higher radix, Karatsuba,
  Toom-Cook, Schönhage-Strassen
- Benchmark suite: commutativity, associativity, distributivity,
  factoring, constant multiplication, square identity, real-world proofs
- Key finding: **Comba encoding is 30x faster than baseline on
  commutativity at BW=11 with CaDiCaL**, despite having 2x more clauses
- Key finding: **Dadda/Wallace are best on real-world benchmarks**
- Key finding: **Bitwuzla solves algebraic identities instantly via
  word-level normalization, not bit-blasting**

## Key Questions from Adder Investigation Perspective

1. **Does Comba produce glue-1 learned clauses?** The Comba encoding
   uses balanced popcount trees — similar to BK's carry tree. Does this
   create the same BCP cascade → glue-1 → fewer conflicts pattern?

2. **Does the BVE polarity alignment apply?** Can we add redundant AND
   gates to the multiplier encoding (like g-only for adders) to trigger
   BVE cascades?

3. **What is the SAT/UNSAT asymmetry for multiplication?** Commutativity
   is UNSAT (always true). Factoring is SAT. Do different encodings
   help differently for SAT vs UNSAT multiplication problems?

4. **Why does Comba help CaDiCaL but not MiniSat?** The adder
   investigation showed BK helps CaDiCaL but hurts MiniSat. Is the
   same solver-specific effect at play?

5. **Can the adder encoding (BK, g-only) improve the internal additions
   within the multiplier?** The multiplier uses adders for partial
   product accumulation. Do BK or g-only help these internal additions?

## Investigation Plan

### Phase 1: Reproduce and profile existing encodings
- Build the multiplier encoding branch
- Reproduce the benchmark results
- Profile CaDiCaL with logging: conflicts, decisions, propagations,
  learned clause quality (glue distribution)
- Compare BCP depth (propagations per decision) across encodings

### Phase 2: Apply adder insights
- Test BK adder inside each multiplier encoding
- Test g-only (redundant AND) inside each multiplier encoding
- Analyze learned clause quality for Comba vs baseline
- Check BVE elimination rates

### Phase 3: Novel approaches
- Based on findings from Phase 1-2, develop new encoding strategies
- Test word-level preprocessing (Bitwuzla-style normalization)
- Investigate hybrid approaches (Comba + BK, Comba + g-only)

## References

- Adder encoding investigation: `doc/adder-encoding-investigation.md`
- Multiplier encoding research: `doc/architectural/multiplication-encoding-research.md`
  (on branch `tautschnig/feature/multiplier-encoding`)
- Brain 2021, "Further Steps Down The Wrong Path"
- Brain et al. 2016, "Automatic Generation of Propagation Complete SAT Encodings"
- Kaufmann & Biere 2023, AMulet2 algebraic verification

## Phase 1: Initial Profiling

### Baseline Multiplication (shift-add with ripple carry)

Commutativity benchmark (`a*b == b*a`):

| BW | Time | Vars | Clauses |
|----|------|------|---------|
| 7 | 0.12s | — | — |
| 9 | 1.94s | 427 | 1,749 |
| 11 | 55.9s | — | — |
| 13 | >120s | — | — |

### Learned Clause Quality (BW=9, baseline)

| Metric | Multiplication | Addition (ripple) | Addition (BK) |
|--------|---------------|-------------------|---------------|
| Learned clauses | 87,588 | 16,961 | 629 |
| Avg clause size | **32.7** | 8.0 | 5.1 |
| Avg glue | **7.9** | 4.7 | 1.0 |
| Glue ≤ 1 | **0%** | 15% | 95% |
| Conflicts | 88,733 | 21,187 | 661 |
| Props/dec | 36,5,5,5,4 | 4,4,4,4 | 8,14,8,12 |

### Key Observations

1. **Zero glue-1 clauses.** Multiplication conflicts span many decision
   levels (avg glue 7.9). The partial product structure creates
   dependencies across all input bits, preventing single-level conflicts.

2. **Huge learned clauses (32.7 literals).** Each conflict involves many
   variables from the multiplication circuit. This is 4x larger than
   ripple carry addition and 6x larger than BK addition.

3. **First decision triggers 36 propagations** — the partial product
   AND gates cascade. But subsequent decisions only trigger 4-5 props,
   similar to ripple carry. The multiplication structure doesn't
   sustain deep BCP cascades.

4. **Adder encoding doesn't help.** BK, g-only, and BK+simp produce
   identical results because the multiplier uses its own adder encoding
   (multiplier_adder_encoding = RIPPLE_CARRY). g-only inside the
   multiplier (g-mult) gives a modest 1.13x at BW=11.

### Implication for Encoding Strategy

The multiplication problem is fundamentally different from addition:
- Addition has a single sequential chain (carry) → BK's tree helps
- Multiplication has a GRID of partial products → no single chain to optimize
- The grid creates multi-level dependencies → high-glue learned clauses
- No tree structure can reduce the grid to a single chain

The Comba encoding (from the research branch) reportedly achieves 30x
speedup by using balanced popcount trees for column reduction. This
may work by creating more structured BCP cascades within each column,
even though the cross-column dependencies remain.

### Next: Profile Comba encoding
Need to build the multiplier encoding branch and compare Comba's
learned clause quality with baseline.

## Phase 1: Comba Profiling Results

### Performance (commutativity benchmark)

| BW | Baseline | Comba | Speedup |
|----|----------|-------|---------|
| 7 | 0.12s | 0.07s | 1.7x |
| 9 | 2.01s | 0.24s | **8.4x** |
| 11 | 61.3s | 1.76s | **35x** |
| 13 | >120s | — | — |

### Learned Clause Quality (BW=9, commutativity)

| Metric | Baseline | Comba | Ratio |
|--------|----------|-------|-------|
| Time | 1.94s | 0.24s | 8.1x faster |
| Variables | 427 | 627 | 1.47x more |
| **Conflicts** | **88,733** | **10,831** | **8.2x fewer** |
| Avg clause size | 32.7 | 20.6 | 37% smaller |
| Avg glue | 7.9 | 6.2 | 22% lower |
| Glue ≤ 1 | 0% | 2% | Slight improvement |
| Props/dec (first) | 36 | 47 | 30% deeper |

### Analysis

Comba's mechanism is DIFFERENT from BK's:
- **BK for adders:** 95% glue-1 → 32x fewer conflicts (dramatic shift)
- **Comba for multipliers:** 2% glue-1 → 8x fewer conflicts (gradual improvement)

Comba doesn't achieve the glue-1 phenomenon. Instead, it produces
**moderately better** learned clauses: 37% smaller, 22% lower glue.
The improvement is quantitative (better clause quality across the
distribution) rather than qualitative (shift to a different regime).

The popcount tree in Comba creates balanced column reduction that:
1. Produces 30% deeper initial BCP cascades (47 vs 36 props/dec)
2. Creates more structured variable dependencies
3. Enables BVE to eliminate more intermediate variables

This is analogous to the g-only effect for adders (BVE catalyst)
rather than the BK effect (glue-1 shift). The extra variables from
Comba's popcount trees are BVE-friendly, similar to how g-only's
AND gates are BVE-friendly for adders.

### Full Multiplier × Adder Matrix (comm benchmark, CaDiCaL)

| mult × adder | comm-9 | comm-11 | fact-20 |
|-------------|--------|---------|---------|
| shift-add+ripple | 1.97 | 57.5 | 0.05 |
| shift-add+BK | 1.97 | 57.7 | 0.05 |
| shift-add+g-only | 1.97 | 57.7 | 0.05 |
| dadda+ripple | 0.53 | 14.5 | 0.04 |
| **dadda+BK** | **T/O** | **T/O** | 0.05 |
| **dadda+g-only** | **0.71** | **7.92** | 0.04 |
| comba+ripple | 0.24 | 1.76 | 0.06 |
| **comba+BK** | **T/O** | **T/O** | **T/O** |
| **comba+g-only** | **0.16** | 2.97 | 0.07 |

### Critical Findings

1. **BK KILLS multiplier encodings.** Both Dadda+BK and Comba+BK
   time out. BK's extra variables (from the adder inside the multiplier)
   overwhelm the solver. This is the opposite of BK's effect on
   standalone additions.

2. **g-only helps Dadda significantly.** Dadda+g-only gives 7.92s on
   comm-11 (vs 14.5s for Dadda+ripple = 1.8x speedup). The BVE
   catalyst effect works inside the multiplier's Dadda tree additions.

3. **g-only has mixed effects on Comba.** Comba+g-only is fastest at
   BW=9 (0.16s vs 0.24s = 1.5x) but slower at BW=11 (2.97 vs 1.76).
   Comba uses popcount trees (not adders), so g-only adds AND gates
   to the FINAL addition only.

4. **Adder encoding is irrelevant for shift-add.** The shift-add
   multiplier uses its own multiplier_adder_encoding (RIPPLE_CARRY)
   regardless of the --adder-encoding flag.

5. **The best configuration depends on bitwidth:**
   - BW=9: comba+g-only (0.16s)
   - BW=11: dadda+g-only (7.92s) or comba+ripple (1.76s)
   - Factoring: shift-add or dadda (0.04-0.05s)

### Next Steps

- Profile learned clause quality for dadda+g-only vs dadda+ripple
- Test on distributivity and other benchmarks
- Investigate why BK kills multiplier encodings
- Test Karatsuba and Toom-Cook with adder variations

### Corrected Matrix: Multiplier-Internal Adder Is Irrelevant

Testing with independent `--multiplier-adder` control revealed that
the internal adder encoding **doesn't matter** for Dadda, Wallace,
or Comba — they use their own reduction schemes (full adders directly,
not through `adder()`). Only shift-add routes through `adder()`.

The earlier "dadda+g-only = 7.92s" result was from g-only on the
**top-level equality check** (`c == d`), not from inside the multiplier.

### Learned Clause Quality: All Multiplier Encodings (comm BW=9)

| Encoding | Vars | Conflicts | Avg size | Avg glue | Glue≤1 | Time |
|----------|------|-----------|----------|----------|--------|------|
| shift-add | 425 | 88,733 | 32.7 | 7.9 | 0% | 2.26s |
| Wallace | 441 | 53,623 | 26.1 | 7.4 | 0% | 1.35s |
| **Dadda** | **425** | **27,079** | **22.4** | **6.6** | **1%** | **0.59s** |
| **Comba** | **625** | **10,831** | **20.6** | **6.2** | **2%** | **0.22s** |

### BVE Elimination Rates

| Encoding | Vars | Eliminated | Fixed | Remaining |
|----------|------|-----------|-------|-----------|
| shift-add | 425 | 159 | 127 | 139 |
| Dadda | 425 | 141 | 152 | 132 |
| Wallace | 441 | 231 | 71 | 139 |
| Comba | 625 | 234 | 218 | 173 |

### Propagation Depth

| Encoding | First decision props | Pattern |
|----------|---------------------|---------|
| shift-add | 36 | 36, 2, ... |
| Dadda | 27 | 27, 5, 5, ... |
| Comba | 39 | 39, ... |

### Analysis

The multiplier encoding ranking correlates with **conflict count**:
- Comba: 10,831 conflicts (fewest) → 0.22s (fastest)
- Dadda: 27,079 conflicts → 0.59s
- Wallace: 53,623 conflicts → 1.35s
- shift-add: 88,733 conflicts (most) → 2.26s (slowest)

The mechanism is **moderately better learned clauses** (smaller size,
lower glue) rather than the dramatic glue-1 shift seen with BK for
adders. No multiplier encoding achieves significant glue-1 rates.

Comba has the most variables (625 vs 425) but the fewest remaining
after BVE (173 vs 132-139). The extra popcount tree variables are
efficiently eliminated, similar to the g-only BVE catalyst for adders.

### Key Insight: Top-Level Encoding Matters More

The g-only benefit on multiplication benchmarks comes from the
**equality check** (`c == d`), not from the multiplication itself.
Setting `--adder-encoding adaptive` (g-only) helps the top-level
comparison, giving an additional 1.8x on top of any multiplier encoding.

Best configurations:
- **comba + g-only(top)**: 0.16s at BW=9 (12x vs baseline)
- **dadda + g-only(top)**: 7.84s at BW=11 (7x vs baseline)


## Open Investigation Leads

### Priority 1: Embedded adder encodings in reduction trees

Dadda/Wallace/Comba call `full_adder()` directly (not through `adder()`).
The 14-clause propagation-complete full_adder is used for every reduction
step. Investigations:

a. **Simpler full_adder inside reduction trees** — test whether fewer
   clauses (not propagation-complete) works better, similar to how
   simple-ripple helped popcount's multiplication.

b. **g-only at the full_adder level** — add redundant AND(a,b) for each
   full_adder call inside Dadda/Wallace. Requires modifying full_adder()
   or adding a wrapper. Could trigger BVE cascades within the reduction tree.

c. **Alternative popcount implementations for Comba** — Comba uses
   parallel bit counting with AND/XOR trees. Test sorting networks or
   different tree structures.

d. **BK vs ripple for Dadda/Wallace final addition** — the carry-save
   form produces two rows; the final addition IS routed through `adder()`.
   Test BK, g-only, and other adder encodings for this final step only.

### Priority 2: Radix multiplier adder encoding

The radix-8 multiplier has THREE types of embedded operations:

a. **Pre-computation additions** (`x*3 = x + x<<1`, `x*5`, `x*7`) —
   these ARE routed through `adder()`, so BK/g-only/multiplier-adder
   all apply. These are standalone additions where our adder insights
   should directly help.

b. **Partial product selection** — MUX/conditional logic to select
   pre-computed multiples. The MUX structure we investigated for arrays.

c. **Final accumulation** — uses Dadda/Wallace/Comba/shift-add reduction.
   The multiplier encoding choice applies here.

The radix multiplier is the ONE encoding where adder encoding choice
could make a real difference (via the pre-computation additions).

### Priority 3: Cross-benchmark validation

Test all multiplier × adder combinations on:
- Distributivity (`a*(b+c) == a*b + a*c`)
- Factoring (find `p*q == n`)
- Constant multiplication (`a*3 == a+a+a`)
- Square identity (`(a+b)^2 == a^2 + 2ab + b^2`)
- Real-world benchmarks (aws_mul_checked, etc.)

### Priority 4: Karatsuba and Toom-Cook with new controls

Test Karatsuba and Toom-Cook with:
- Independent multiplier-adder encoding
- g-only on top-level
- Different sub-multiplier encodings (Karatsuba uses recursive multiplication)

### Previously completed

- Full multiplier × adder matrix (Phase 1)
- Learned clause quality for all multiplier encodings
- BVE elimination rates
- Propagation depth analysis
- Corrected understanding: multiplier-internal adder irrelevant for Dadda/Wallace/Comba
- g-only benefit comes from top-level equality check

## Priority 1a Results: Simple Full Adder Inside Reduction Trees

| Config | comm-9 | comm-11 | comm-13 |
|--------|--------|---------|---------|
| dadda | 0.53 | 14.3 | T/O |
| **dadda+simple-fa** | 0.56 | **8.06** | T/O |
| wallace | 1.82 | 52.1 | T/O |
| **wallace+simple-fa** | 1.27 | **48.0** | T/O |
| **comba** | **0.24** | **1.75** | **8.17** |
| comba+simple-fa | 0.31 | 2.02 | 10.6 |

**Simple-fa helps Dadda (1.8x at BW=11)** by using fewer clauses per
full adder in the reduction tree. The non-propagation-complete encoding
works better inside Dadda because the reduction tree's structure doesn't
require carry chain propagation completeness — each full adder is
independent (carry-save form).

**Simple-fa hurts Comba** because Comba uses popcount trees (not full
adders for reduction). The simple-fa only affects the FINAL addition
in Comba, where propagation completeness matters.

### Best Combinations with g-only Top-Level

| Config | comm-9 | comm-11 | comm-13 |
|--------|--------|---------|---------|
| comba+g-top | **0.16** | 2.94 | 12.1 |
| **comba+sfa+g-top** | 0.35 | 3.24 | **6.08** |
| dadda+g-top | 0.70 | 7.81 | T/O |

**comba+sfa+g-top is best at BW=13** (6.08s). The simple-fa helps
Comba's final addition at larger bitwidths where the carry chain
is longer.
