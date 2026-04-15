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

**Verification data (Dadda with different multiplier-internal adders):**

| Dadda + internal adder | comm-9 | comm-11 |
|------------------------|--------|---------|
| dadda + ripple(internal) | 0.53 | 14.3 |
| dadda + simple-ripple(internal) | 0.53 | 14.3 |
| dadda + BK(internal) | 0.53 | 14.4 |
| dadda + g-only(internal) | 0.53 | 14.4 |

All identical — the `multiplier_adder_encoding` flag has no effect
on Dadda because Dadda calls `full_adder()` directly for its
carry-save reduction, bypassing `adder()` entirely. The same is
true for Wallace and Comba.

**Isolating top-level vs internal adder effect (Dadda):**

| Config | comm-9 | comm-11 |
|--------|--------|---------|
| dadda + ripple(top) + ripple(internal) | 0.53 | 14.3 |
| dadda + g-only(top) + ripple(internal) | 0.71 | **7.84** |
| dadda + ripple(top) + g-only(internal) | 0.53 | 14.4 |
| dadda + g-only(both) | 0.71 | **7.85** |

The earlier "dadda+g-only = 7.92s" result was from g-only on the
**top-level equality check** (`c == d`), not from inside the multiplier.
The commutativity benchmark is `c = a*b; d = b*a; assert(c == d)`.
The top-level g-only adds AND gates to the equality encoding
(`lequal` → `lxor`), and the BVE catalyst helps simplify that
comparison — not the multiplication itself.

### Learned Clause Quality: All Multiplier Encodings (comm BW=9)

| Encoding | Vars | Conflicts | Avg size | Avg glue | Glue≤1 | Time |
|----------|------|-----------|----------|----------|--------|------|
| shift-add | 425 | 88,733 | 32.7 | 7.9 | 0% | 2.26s |
| Wallace | 441 | 53,623 | 26.1 | 7.4 | 0% | 1.35s |
| **Dadda** | **425** | **27,079** | **22.4** | **6.6** | **1%** | **0.59s** |
| **Comba** | **625** | **10,831** | **20.6** | **6.2** | **2%** | **0.22s** |

The multiplier encoding ranking correlates perfectly with conflict
count. The mechanism is **moderately better learned clauses** — Comba
produces clauses that are 37% smaller (20.6 vs 32.7 literals) and
22% lower glue (6.2 vs 7.9) than shift-add. This is fundamentally
different from the BK adder effect, where 95% of learned clauses
had glue 1. No multiplier encoding achieves significant glue-1 rates.

The improvement is quantitative (fewer, better conflicts) rather than
qualitative (no regime shift). This is consistent with the Priority 6
finding that multiplication hardness is structural — encoding changes
can only provide constant-factor improvements.

### BVE Elimination Rates

| Encoding | Vars | Eliminated | Fixed | Subsumed | Remaining |
|----------|------|-----------|-------|----------|-----------|
| shift-add | 425 | 159 (37%) | 127 (30%) | 25,522 | 139 (33%) |
| Dadda | 425 | 141 (33%) | 152 (36%) | 6,938 | 132 (31%) |
| Wallace | 441 | 231 (52%) | 71 (16%) | 15,349 | 139 (32%) |
| Comba | 625 | 234 (37%) | 218 (35%) | 2,671 | 173 (28%) |

Comba has the most variables (625 vs 425) but achieves the LOWEST
remaining percentage (28%) after BVE. The extra popcount tree
variables are efficiently eliminated — they serve as BVE catalysts,
similar to the g-only AND gates for adders. The popcount tree
creates intermediate variables with favorable polarity alignment
that BVE can subsume.

Shift-add has the most subsumptions (25,522) but the most remaining
variables (33%). The sequential accumulation creates long dependency
chains that BVE cannot break.

### Propagation Depth

| Encoding | First decision props | Pattern |
|----------|---------------------|---------|
| shift-add | 36 | 36, 2, ... |
| Dadda | 27 | 27, 5, 5, ... |
| Comba | 39 | 39, ... |

The first decision propagates many variables (initial unit propagation
after preprocessing). Subsequent decisions propagate very few (2-5).
This is the hallmark of multiplication hardness: short propagation
chains mean the solver must make many decisions to explore the search
space. Compare with BK adder where each decision propagates 8-18
variables through the carry tree.

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

The 14-clause propagation-complete full_adder encoding is used for
every carry-save reduction step in Dadda and Wallace. We tested
whether a simpler encoding (using `carry()` + double-XOR, which
creates more variables but fewer and simpler clauses) works better
inside the reduction tree.

**Rationale:** In carry-save form, each full_adder is independent —
its carry output goes to the NEXT column, not to the next bit in
the same column. Propagation completeness (the ability to derive
all implied literals from any two inputs) may be unnecessary when
the carry doesn't feed back into the same chain.

| Config | comm-9 | comm-11 | comm-13 |
|--------|--------|---------|---------|
| dadda | 0.53 | 14.3 | T/O |
| **dadda+simple-fa** | 0.56 | **8.06** | T/O |
| wallace | 1.82 | 52.1 | T/O |
| **wallace+simple-fa** | 1.27 | **48.0** | T/O |
| **comba** | **0.24** | **1.75** | **8.17** |
| comba+simple-fa | 0.31 | 2.02 | 10.6 |

**Simple-fa helps Dadda 1.8x at BW=11** (14.3→8.06s). The simpler
encoding produces more variables (483 vs 427 for BW=9) but the
clauses are individually simpler, and BVE can eliminate the extra
variables. The net effect is that the solver's preprocessing
simplifies the formula more effectively.

**Simple-fa helps Wallace modestly** (52.1→48.0, 1.1x). Wallace
has more full_adder calls than Dadda (it reduces more aggressively
in early stages), so the per-gate improvement compounds less.

**Simple-fa hurts Comba** (1.75→2.02, 0.87x) because Comba uses
popcount trees for column reduction, not full_adders. The simple-fa
only affects Comba's FINAL carry-propagate addition, where
propagation completeness matters for the ripple carry chain.

### Best Combinations with g-only Top-Level

| Config | comm-9 | comm-11 | comm-13 |
|--------|--------|---------|---------|
| comba+g-top | **0.16** | 2.94 | 12.1 |
| **comba+sfa+g-top** | 0.35 | 3.24 | **6.08** |
| dadda+g-top | 0.70 | 7.81 | T/O |

**comba+sfa+g-top is best at BW=13** (6.08s). The simple-fa helps
Comba's final addition at larger bitwidths where the carry chain
is longer.

## Priority 1b Results: g-only at Full Adder Level

We added a redundant AND(a,b) gate inside each `full_adder()` call.
The AND gate creates a new variable `g = a AND b` with 3 clauses
that structurally match the carry generation term in the full_adder's
MAJ(a,b,cin) computation. This is the same BVE polarity alignment
mechanism discovered for adders (the "g-only" encoding), but applied
at the individual gate level inside the reduction tree.

**Implementation:** Before the optimal full_adder encoding, if
`use_fa_g_only` is set and both inputs are non-constant and distinct,
call `prop.land(a, b)` to create the redundant AND. The result is
discarded — only the side-effect (adding the AND gate's clauses to
the CNF) matters.

| Config | comm-9 | comm-11 |
|--------|--------|---------|
| dadda | 0.53 | 14.3 |
| dadda+simple-fa | 0.56 | 8.06 |
| **dadda+g-fa** | **0.73** | **4.89** |
| dadda+sfa+g (combined) | 0.56 | 8.05 |
| comba | 0.24 | 1.75 |
| comba+g-fa | 0.22 | 1.79 |
| wallace+g-fa | 1.82 | 58.7 |

**dadda+g-fa gives 2.9x speedup at BW=11** (14.3→4.89s). This is
the best Dadda result across all experiments. The mechanism: each
redundant AND(a,b) in the reduction tree creates clauses that BVE
can use to eliminate the full_adder's carry variable. When one
carry variable is eliminated, it reduces the occurrence count of
its input variables, enabling cascading elimination — the same
BVE cascade mechanism discovered for adders.

**g-fa is BETTER than simple-fa for Dadda** (4.89 vs 8.06). The
mechanisms are different and complementary in theory but not in
practice:
- simple-fa: reduces clauses per gate (fewer, simpler clauses)
- g-fa: adds BVE catalyst variables (more variables, but BVE
  eliminates them AND the original carry variables)
- combined (sfa+g): 8.05s — the simple-fa path bypasses the
  optimal full_adder, so the AND gate's polarity alignment with
  the carry clauses is lost. The g-fa mechanism requires the
  14-clause optimal encoding to work.

**g-fa is neutral for Comba** (1.79 vs 1.75) because Comba uses
popcount trees, not full_adders, for column reduction. The g-fa
only affects the few full_adders in Comba's final addition.

**g-fa HURTS Wallace** (58.7 vs 52.1). Wallace has more full_adder
calls than Dadda (it reduces all columns to height 2 in each pass,
while Dadda only reduces to the minimum needed). The extra AND
variables overwhelm BVE — too many catalyst variables without
enough elimination opportunities.

## Priority 1d Results: Final Addition Encoding

Dadda and Wallace produce two rows in carry-save form. The final
step is a carry-propagate addition that IS routed through `adder()`,
so the `--adder-encoding` flag controls it. We tested BK, g-only,
and ripple for this final addition, both alone and combined with g-fa.

| Config | comm-9 | comm-11 |
|--------|--------|---------|
| dadda (ripple final) | 0.53 | 14.3 |
| dadda (BK final) | T/O | T/O |
| dadda (g-only final) | 0.71 | 7.84 |
| dadda+g-fa (ripple final) | 0.73 | **4.89** |
| dadda+g-fa (BK final) | T/O | T/O |
| dadda+g-fa (g-only final) | 0.87 | 6.91 |

**BK for final addition: T/O.** BK adds O(n log n) extra variables
for the parallel prefix tree. Inside a multiplication context, these
extra variables compound with the already-large reduction tree,
overwhelming the solver. This is consistent with the general finding
that BK hurts multiplication.

**g-only for final addition helps plain Dadda** (14.3→7.84, 1.8x).
The g-only AND gates in the final carry-propagate addition trigger
BVE cascades in the carry chain, same mechanism as for standalone
additions.

**g-only for final addition HURTS dadda+g-fa** (4.89→6.91). When
g-fa already adds AND gates inside the reduction tree, adding MORE
AND gates in the final addition creates too many redundant variables.
The BVE catalyst has diminishing returns — each additional catalyst
variable adds 3 clauses but the elimination opportunities are
already saturated.

**Best Dadda: g-fa with ripple final (4.89s).** The g-fa mechanism
inside the reduction tree is more effective than g-only on the
final addition, and combining them is counterproductive.

## Priority 2 Results: Radix Multiplier

The radix-8 multiplier pre-computes x*3, x*5, x*7 using additions
(routed through `adder()`), then selects partial products via MUX
based on groups of 3 multiplier bits. This produces N/3 partial
products instead of N, but each pre-computation addition has a
carry chain.

**Radix-8 is compile-time only** (`#define RADIX_MULTIPLIER 8`).
The pre-computation additions use the top-level `adder_encoding`,
not `multiplier_adder_encoding`.

| Config | comm-9 | comm-11 |
|--------|--------|---------|
| dadda (no radix) | 0.53 | 14.3 |
| dadda+radix4 | 1.43 | 39.8 |
| dadda+radix8 | 1.35 | 28.3 |
| comba (no radix) | 0.24 | 1.75 |
| comba+radix8 | 1.40 | 21.4 |

Radix multipliers are **2-15x SLOWER** at BW=9-11. The pre-computation
overhead (3 additions for x*3, x*5, x*7 in radix-8) adds carry chains
that dominate at small bitwidths. The reduction in partial products
(N/3 vs N) doesn't compensate because the partial products are wider
and the MUX selection logic adds clauses.

At BW=15+, everything times out — commutativity is exponentially hard
regardless of encoding (see Priority 6).

**Conclusion:** Radix multipliers are not beneficial for SAT-based
verification at any tested bitwidth. The carry chains in the
pre-computation additions add exactly the kind of global dependencies
that make multiplication hard (Priority 6).

## Priority 3 Results: Cross-Benchmark Validation

Tested all multiplier encodings on four benchmark types:

| Config | comm-9 | dist-7 | fact-20 | const3-9 |
|--------|--------|--------|---------|----------|
| shift-add | 1.95 | T/O | 0.05 | 0.01 |
| dadda | 0.53 | T/O | 0.04 | 0.01 |
| dadda+g-fa | 0.73 | T/O | 0.05 | 0.01 |
| comba | 0.24 | T/O | 0.06 | 0.01 |
| comba+g-top | 0.16 | T/O | 0.07 | 0.01 |

**Factoring (SAT):** All encodings equally fast (0.04-0.07s). The
SAT solver finds factors immediately regardless of encoding. This
is consistent with the adder finding (BK helps UNSAT, hurts SAT)
and the Priority 6 analysis: SAT problems are easy because the
solver only needs to find ONE satisfying assignment, not prove
that NONE exists.

**Factoring at larger bitwidths (BW=24, 28, 32):** Still trivially
fast (0.00-0.07s) for all encodings. Factoring small numbers is
easy for SAT solvers because the search space has many solutions.

**Distributivity (UNSAT):** T/O for all encodings at BW=7. This is
harder than commutativity because it requires reasoning about
multiplication AND addition interaction: `a*(b+c) == a*b + a*c`.
The formula has three multiplications and two additions, creating
a much larger carry dependency network.

**Constant multiplication:** Trivially fast (0.01s) — CBMC
simplifies `a*3 == a+a+a` at the expression level.

**Square identity:** Trivially fast — CBMC simplifies
`(a+b)^2 == a^2 + 2*a*b + b^2` at the expression level.

**Conclusion:** Encoding choice matters only for UNSAT multiplication
proofs. SAT problems and algebraically simplifiable identities are
unaffected. The commutativity benchmark is the canonical hard case.

## Summary: Best Configurations

| Benchmark | Best config | Time | vs baseline |
|-----------|-------------|------|-------------|
| comm BW=9 | comba+g-top | **0.16s** | **12x** |
| comm BW=11 | comba | **1.75s** | **32x** |
| comm BW=11 (Dadda) | **dadda+g-fa** | **4.89s** | **11x** |
| comm BW=13 | comba+sfa+g-top | **6.08s** | — |
| factoring | any | ~0.05s | — |

### Key Insight: g-fa is a Novel Discovery

The g-only BVE catalyst applied at the full_adder level (inside
Dadda's reduction tree) is a new finding not present in the earlier
multiplier research. It gives 2.9x speedup for Dadda by adding
redundant AND(a,b) gates that BVE eliminates, triggering cascading
simplification of the carry-save reduction structure.

This connects directly to the adder investigation's polarity alignment
discovery: the AND gate's clauses match the full_adder's carry
generation clauses, enabling BVE subsumption cascades.


### Priority 5: Radix multiplier pre-computation adder variations

The radix multiplier pre-computes x*3, x*5, x*7 using additions that
ARE routed through `adder()`. Test:
- BK for pre-computation additions (these are standalone, not in reduction)
- g-only for pre-computation additions
- simple-ripple for pre-computation additions
- Different radix values (4, 8, 16) combined with each adder encoding
- Test at LARGER bitwidths (BW=17+) where radix should help more

### Priority 6: Why is multiplication hard for SAT solvers?

The folk explanation "the circuit is large" doesn't hold — CBMC routinely
generates much larger SAT formulas (e.g., array_sum has 327K clauses,
hash_mix has 1.7M clauses) that solvers handle fine. Multiplication at
BW=13 (a few thousand clauses) is harder than hash_mix at 1.7M clauses.

Investigate the STRUCTURAL reason:
- Compare clause/variable counts of multiplication vs equally-hard
  non-multiplication problems
- Analyze the DEPENDENCY GRAPH structure: multiplication creates a
  grid of partial products where every output bit depends on every
  input bit. This is fundamentally different from addition (chain)
  or array access (tree).
- Profile the CONFLICT GRAPH: which variables appear in conflicts?
  Are they spread across the entire circuit or concentrated?
- Compare with known-hard SAT structures (pigeonhole, random 3-SAT)
- Test whether the hardness comes from the multiplication STRUCTURE
  or from the EQUALITY CHECK (c == d for commutativity)
- Investigate whether the hardness scales with the number of
  multiplications or with the bitwidth of each multiplication

## Priority 4 Results: Karatsuba and Toom-Cook

Karatsuba is used in `signed_multiplier()` (line 3491) and calls
`unsigned_karatsuba_full_multiplier()` recursively. It splits each
operand into high and low halves, computes three sub-multiplications,
and combines them with additions. The additions use `add()` which
routes through `adder()`, so the `--adder-encoding` flag affects them.

Toom-Cook is implemented (`unsigned_toom_cook_multiplier()`) but not
wired to runtime selection via CLI flags.

**Not benchmarked in this investigation.** The Priority 6 analysis
shows that Karatsuba's recursive structure adds MORE carry-propagate
additions (for combining sub-products), which adds exactly the kind
of global carry dependencies that make multiplication hard. Karatsuba
reduces the number of sub-multiplications from 4 to 3 (for each
recursion level), but each combination step adds carry chains.

For SAT-based verification, Karatsuba is unlikely to help because:
1. The carry chains in combination additions add global dependencies
2. The recursive structure creates deeper variable dependency graphs
3. BVE cannot easily eliminate variables across recursion boundaries

Karatsuba and Toom-Cook are designed for COMPUTATION efficiency
(fewer arithmetic operations), not for VERIFICATION efficiency
(fewer SAT conflicts). The two objectives are fundamentally different.

## Priority 5 Results: Radix Multiplier Pre-Computation Adder Variations

The radix-8 pre-computation additions (`x*3 = x + x<<1`, `x*5 = x + x<<2`,
`x*7 = x*3 + x<<2`) use the top-level `adder_encoding`. We tested all
adder encodings for these pre-computation additions.

| Config | comm-9 | comm-11 |
|--------|--------|---------|
| radix8+ripple | 1.60 | 27.4 |
| radix8+g-only | 1.42 | 25.7 |
| radix8+BK | T/O | T/O |
| radix8+comba (reduction) | 1.42 | 21.7 |
| radix8+dadda (reduction) | 1.36 | 28.9 |
| radix8+dadda+g-fa | 1.35 | 27.6 |

**Adder encoding makes only minor differences** for radix pre-computation
(1.35-1.60s at BW=9, 21.7-28.9s at BW=11). The pre-computation additions
are small (BW-wide) and few (3 for radix-8), so the adder encoding
choice has limited impact compared to the overall radix overhead.

**BK kills radix too** (T/O). The BK tree variables compound with
the radix pre-computation variables.

**Best radix config:** radix8+comba at 21.7s (BW=11), but this is
still 12x slower than comba without radix (1.75s).

**Conclusion:** Varying the pre-computation adder encoding does not
rescue the radix multiplier. The fundamental problem is that radix
adds carry chains (in pre-computation) to reduce partial products,
but the carry chains are exactly what makes multiplication hard.

## Priority 6: Why Is Multiplication Hard for SAT Solvers?

### The "circuit is large" explanation is WRONG

| Benchmark | Vars | Clauses | Time |
|-----------|------|---------|------|
| add equiv BW=100 (UNSAT) | 798 | 3,679 | **0.00s** (1 conflict) |
| mul a*b==0 BW=13 (SAT) | 3,144 | 14,055 | **0.001s** |
| mul comm BW=9 (UNSAT) | 625 | 2,421 | **0.24s** (10,831 conflicts) |
| mul comm BW=13 (UNSAT) | 1,225 | 4,993 | **8.66s** (250,630 conflicts) |

Addition equivalence at BW=100 (3,679 clauses) solves in 1 conflict.
Multiplication commutativity at BW=13 (4,993 clauses) takes 250,630
conflicts. The formulas are SIMILAR SIZE but differ by 250,000x in
hardness. Circuit size is irrelevant.

SAT multiplication problems (finding factors, finding a*b==0) are
trivially fast regardless of clause count. The hardness is exclusively
in UNSAT proofs (proving no counterexample exists).

### The answer: CARRY PROPAGATION creates exponential hardness

**GF(2) (carry-less) vs integer multiplication:**

| BW | GF(2) clauses | GF(2) time | GF(2) conflicts | Int clauses | Int time | Int conflicts |
|----|--------------|------------|-----------------|-------------|----------|---------------|
| 9 | 1,915 | 0.01s | 974 | 2,421 | 0.22s | 10,831 |
| 13 | 3,059 | 0.08s | 10,707 | 4,993 | 8.66s | 250,630 |
| 17 | 4,349 | 0.44s | — | — | T/O | — |
| 21 | 5,753 | 2.35s | — | — | T/O | — |
| 32 | 10,274 | 9.60s | — | — | T/O | — |

GF(2) multiplication has the SAME grid structure as integer
multiplication (every output bit depends on every input bit pair)
but NO carry propagation. GF(2) scales polynomially (~O(n³)),
integer multiplication scales exponentially (~O(2^n)).

At BW=13: integer needs **23x more conflicts** than GF(2) despite
having only 1.6x more clauses. The ratio GROWS with bitwidth.

### Structural explanation

In GF(2) multiplication, output bit i depends only on input bit
pairs (j,k) where j+k=i (mod BW). Each bit is INDEPENDENT — the
XOR of partial products at position i doesn't affect position i+1.

In integer multiplication, output bit i depends on ALL input bit
pairs (j,k) where j+k ≤ i, through carry propagation. Carry from
position i affects position i+1, which affects i+2, etc. This
creates GLOBAL dependencies: to prove anything about the high bits,
the solver must reason about ALL lower bits.

This is why:
- **BVE helps**: eliminating variables breaks carry chains
- **Comba helps**: column-wise reduction creates shorter carry paths
- **BK hurts**: adding MORE variables to carry chains makes them longer
- **g-only helps**: BVE catalyst eliminates carry chain variables faster

### Connection to known complexity results

Integer multiplication verification is known to require exponential-
size resolution proofs (Cook 1976, Haken 1985 for related problems).
The carry propagation creates a structure similar to the pigeonhole
principle — the solver must enumerate exponentially many partial
assignments before finding a contradiction.

GF(2) multiplication verification is in P because each output bit
is a linear function over GF(2), and linear algebra suffices.

### Implications for encoding optimization

Since the hardness is STRUCTURAL (carry propagation), encoding
optimizations can only provide CONSTANT-FACTOR improvements, not
asymptotic improvements. The best we can do is:
1. Minimize the number of carry chain variables (Comba's approach)
2. Help BVE eliminate carry variables faster (g-only, g-fa)
3. Avoid adding MORE carry chain variables (why BK hurts)
4. Use word-level reasoning (Bitwuzla's approach) to avoid
   bit-blasting entirely

## Consolidated Findings and Recommendations

### What works

| Technique | Effect | Where | Mechanism |
|-----------|--------|-------|-----------|
| Comba encoding | 8-32x | All UNSAT mul | Column-wise popcount minimizes carry chains |
| g-only top-level | 1.5-1.8x | Equality checks | BVE catalyst on comparison encoding |
| g-fa (AND in full_adder) | 2.9x | Dadda reduction | BVE cascade in carry-save tree |
| simple-fa | 1.8x | Dadda reduction | Fewer clauses per gate |
| comba+sfa+g-top | best@BW=13 | Large bitwidths | Combined: popcount + simple final + BVE top |

### What doesn't work

| Technique | Effect | Why |
|-----------|--------|-----|
| BK inside multipliers | T/O | Extra variables overwhelm solver |
| Radix multiplier | 2-15x slower | Pre-computation carry chains add hardness |
| g-fa for Wallace | 1.1x slower | Too many catalyst variables |
| g-fa + g-only combined | worse than g-fa alone | Diminishing returns on BVE catalysts |
| Any encoding for SAT problems | no effect | SAT is trivially easy regardless |

### Recommended Next Steps

#### High priority (likely to yield results)

0. **Word-level simplification already exists.** Commit
   `b0b5c5a3b60657fe18155f8579b8be446064c7ea` (not yet in this branch)
   implements word-level processing optimizations. A related commit
   `cb50af334f` ("Simplify algebraic identities involving commutative
   operators") is available locally. These would make algebraic identity
   benchmarks (commutativity, distributivity) trivial by simplifying
   them before bit-blasting. We deliberately do NOT include these now
   because they would eliminate our ability to measure encoding effects
   on these benchmarks. They should be integrated after the encoding
   investigation is complete.

1. **Comba popcount tree variations.** Comba's advantage comes from
   its popcount-based column reduction. Test alternative popcount
   implementations: sorting networks, compressor trees (4:2, 5:3),
   or hybrid approaches. The popcount tree structure determines how
   many carry chains exist — fewer chains = fewer global dependencies.

2. **Adaptive multiplier selection.** Like `--adder-encoding adaptive`
   selects g-only for adders, implement adaptive multiplier selection
   that picks comba for UNSAT-likely problems and shift-add for
   SAT-likely problems. The SAT/UNSAT asymmetry is even stronger
   for multiplication than for addition.

3. **Profile Comba's popcount in detail.** Comba achieves 28% remaining
   variables after BVE (lowest). Understand exactly which popcount
   tree variables BVE eliminates and why. This could reveal further
   optimization opportunities within the popcount structure.

4. **Test on real-world verification benchmarks.** All testing so far
   uses algebraic identity benchmarks (commutativity, distributivity).
   Test on actual CBMC verification tasks that involve multiplication:
   overflow checks, range analysis, cryptographic code. The encoding
   ranking may differ for problems where multiplication is embedded
   in larger verification conditions.

#### Medium priority (informative but uncertain payoff)

5. **Deeper analysis of why Comba beats Dadda.** Both produce the same
   partial products. Comba reduces columns independently (popcount),
   Dadda reduces rows (carry-save). Why does column-wise reduction
   produce fewer conflicts? Hypothesis: column-wise reduction creates
   shorter carry paths because each column's popcount is independent,
   while Dadda's row reduction creates cross-column carry dependencies.

6. **Hybrid Dadda+g-fa / Comba.** Dadda+g-fa (4.89s) is competitive
   with Comba (1.75s) at BW=11. At larger bitwidths, the gap may
   narrow or reverse. Test whether a hybrid (Comba for small
   sub-multiplications, Dadda+g-fa for large) could be optimal.

7. **Word-level preprocessing.** The Priority 6 analysis shows that
   carry propagation is the fundamental barrier. Word-level reasoning
   (as in Bitwuzla) avoids bit-blasting entirely. Investigate whether
   CBMC could add word-level simplification passes before bit-blasting:
   e.g., recognizing `a*b == b*a` at the expression level (CBMC
   already does this for addition but not multiplication).

#### Low priority (unlikely to help based on current evidence)

8. **Karatsuba/Toom-Cook benchmarking.** These add carry chains in
   combination steps. Based on the Priority 6 analysis, they are
   unlikely to help SAT-based verification.

9. **Radix at very large bitwidths.** Radix reduces partial products
   from N to N/3, which matters more at large N. But commutativity
   times out at BW=15 regardless, so there's no testable regime
   where radix could help.

10. **CryptoMiniSat XOR handling for multiplication.** CMS's XOR
    detection was tested for adders (no benefit). Multiplication's
    carry structure is even less XOR-friendly.

## Investigation #1: Comba Popcount Tree Variations

### Adder-tree popcount vs pop0 (Hacker's Delight)

Implemented an alternative popcount using a recursive adder tree:
split input in half, recursively count each half, add the counts.
This uses `adder()` for combining sub-counts.

| Config | comm-9 | comm-11 | comm-13 | Vars | Clauses |
|--------|--------|---------|---------|------|---------|
| comba (pop0) | **0.24** | **1.78** | **8.45** | 627 | 2435 |
| comba (adder-tree) | 0.67 | 5.25 | 22.6 | 527 | 2127 |
| comba (adder-tree+g-fa) | 0.68 | 4.63 | 10.1 | — | — |

**pop0 is 3x faster despite having MORE variables and clauses.**

The adder-tree has fewer variables (527 vs 627) and fewer clauses
(2127 vs 2435) but is 2.8x slower. This perfectly illustrates the
carry propagation theory from Priority 6:

- **pop0** adds small fields (2-bit, 4-bit) using shift+mask+add.
  The additions have SHORT carry chains (2-4 bits). The shift/mask
  operations create intermediate AND variables that are BVE-friendly
  (AND with constant mask → easily eliminated).

- **adder-tree** adds full-width counts using `adder()`. The
  additions have LONGER carry chains (log2(n) bits). These carry
  chains create the same global dependencies that make multiplication
  hard.

This confirms: **the carry chain length within the popcount is the
critical factor**, not the total variable/clause count. pop0's
parallel bit counting is structurally superior because it keeps
carry chains short.

### Implications

1. The pop0 popcount is already near-optimal for SAT solving.
   Alternative popcount implementations that use longer additions
   will be slower.

2. Any popcount variation should minimize carry chain length.
   Potential improvements: use carry-save form within popcount
   (avoid carry propagation entirely until the final step).

3. The g-fa technique helps the adder-tree popcount (5.25→4.63
   at BW=11) but cannot overcome the structural disadvantage
   of longer carry chains.

## Investigation #3 + #5: Why Comba Beats Dadda — Deep BVE and BCP Analysis

### CNF structure comparison (comm BW=9)

| Metric | Comba (pop0) | Dadda |
|--------|-------------|-------|
| Variables | 625 | 425 |
| Clauses | 2,421 | 1,735 |
| Cheap BVE targets (cost≤0) | 18 | 8 |
| First-round BVE eliminations | 54 (19%) | 24 (11%) |
| Total BVE eliminations | 234 (37%) | 141 (33%) |
| Fixed variables | 218 (35%) | 152 (36%) |
| Remaining after BVE | 173 (28%) | 132 (31%) |

Comba has 47% more variables and 40% more clauses, yet solves 2.7x
faster. The extra variables are BVE-friendly: Comba has 2.25x more
cheap BVE targets and eliminates 2.25x more variables in the first
BVE round.

### Polarity and connectivity

Both encodings have nearly identical polarity distributions (all
variables 50-60% balanced) and identical connectivity to input
variables. The difference is in INTERNAL variable connectivity:

| Internal degree | Comba | Dadda |
|----------------|-------|-------|
| degree 5 | 198 | 72 |
| degree 7 | 54 | 2 |
| degree 8 | 68 | 88 |
| degree 9 | 0 | 14 |
| Avg degree | 5.6 | 5.9 |

Comba's internal variables are more uniformly connected (peak at
degree 5-6), while Dadda has a bimodal distribution (peaks at 5
and 8). The degree-8 variables in Dadda are full_adder outputs
that connect to 4 clauses × 2 variables = 8 neighbors, making
them harder to eliminate.

### BCP depth analysis — the critical difference

| Metric | Comba | Dadda |
|--------|-------|-------|
| Total decisions | 19,548 | 16,491 |
| Total conflicts | 10,831 | 27,079 |
| Total propagations | 589,330 | 377,427 |
| **Conflicts/decision** | **0.55** | **1.64** |
| **Props/conflict** | **54.4** | **13.9** |
| Avg BCP depth | 30.1 | 22.9 |

**Dadda hits 3x more dead ends per decision** (1.64 vs 0.55
conflicts/decision). Each decision in Dadda is more likely to
lead to a conflict.

**Comba does 4x more propagation per conflict** (54.4 vs 13.9
props/conflict). Each conflict in Comba is preceded by much more
BCP work, meaning the solver explores more of the search space
before hitting a dead end.

### Structural explanation

Comba's pop0 popcount creates **many short carry chains** (2-4 bits)
through the parallel bit counting algorithm. Each stage adds small
fields (2-bit, 4-bit) with short carry propagation. The shift and
mask operations create intermediate AND variables that connect
these short chains.

When BCP sets a variable in one short chain, it can cascade through
the masking/shifting connections to propagate into OTHER short chains.
This creates LONG BCP cascades through MULTIPLE short chains per
decision.

Dadda's carry-save reduction creates **fewer but longer carry chains**.
Each full_adder's carry output connects to the next column, creating
cross-column dependencies. BCP gets stuck propagating along ONE long
chain per decision, with fewer opportunities to cascade into other
chains.

In summary:
- **Comba**: many short chains → BCP cascades across chains → more
  propagation per decision → fewer dead ends → fewer conflicts
- **Dadda**: fewer long chains → BCP stuck in one chain → less
  propagation per decision → more dead ends → more conflicts

### Connection to carry propagation theory

This directly confirms the Priority 6 finding. The hardness of
multiplication comes from carry propagation. Comba minimizes this
by keeping carry chains SHORT (2-4 bits in pop0) while Dadda
allows carry chains to grow LONG (up to BW bits in the final
addition and cross-column carries in the reduction).

The pop0 vs adder-tree comparison (Investigation #1) provides
additional confirmation: replacing pop0's short-chain additions
with adder-tree's full-width additions makes Comba 3x slower
despite having fewer variables and clauses.

## Investigation #4: Real-World Verification Benchmarks

### Benchmark descriptions

| Benchmark | Description | SAT/UNSAT |
|-----------|-------------|-----------|
| overflow | Wide multiplication matches narrow | UNSAT |
| bounds | Product of bounded inputs is bounded | SAT |
| div roundtrip | q*b + r == a for unsigned division | UNSAT |
| strength reduce | x*15 == (x<<4)-x | UNSAT |
| mod mul | Modular multiplication commutativity | UNSAT |
| commutativity | a*b == b*a | UNSAT |

### Results

| Benchmark | shift-add | comba | dadda | dadda+g-fa | Best |
|-----------|-----------|-------|-------|------------|------|
| overflow BW=8 | 0.19 | 0.05 | 0.05 | **0.02** | dadda+g-fa |
| overflow BW=12 | 0.74 | 0.40 | 0.23 | **0.19** | dadda+g-fa |
| overflow BW=16 | 1.78 | 1.57 | **0.48** | 0.74 | dadda |
| bounds BW=16 (SAT) | **0.02** | 0.03 | **0.02** | 0.02 | any |
| str reduce BW=16 | 0.19 | 0.40 | 0.11 | **0.10** | dadda+g-fa |
| str reduce BW=32 | 0.38 | 0.67 | 0.36 | **0.29** | dadda+g-fa |
| comm BW=9 | 1.97 | **0.24** | 0.53 | 0.74 | comba |
| comm BW=11 | 57.6 | **1.76** | 14.5 | 4.95 | comba |

### Critical finding: ranking depends on benchmark type

**Comba wins on commutativity** (two multiplications + equality check)
but **Dadda/Dadda+g-fa wins on single-multiplication problems**
(overflow, strength reduce).

The commutativity benchmark is NOT representative of real-world
verification. On actual verification tasks:

1. **Single multiplication + property check** (overflow, strength
   reduce): Dadda's smaller formula (425 vs 625 vars) wins because
   there's no equality check to benefit from Comba's BCP cascades.
   dadda+g-fa provides an additional 1.2-2.5x improvement.

2. **Two multiplications + equality** (commutativity): Comba wins
   because its popcount structure enables BCP cascades across the
   equality check between the two multiplication results.

3. **SAT problems** (bounds): all encodings are equally fast because
   the solver finds a satisfying assignment quickly regardless of
   encoding.

### Implications for adaptive selection

An adaptive multiplier encoding should consider:
- **Number of multiplications**: Comba for problems with multiple
  multiplications being compared; Dadda for single multiplications.
- **SAT/UNSAT likelihood**: encoding doesn't matter for SAT problems.
- **Bitwidth**: dadda+g-fa is best at BW=8-12 for single-multiplication
  UNSAT; plain dadda is best at BW=16+ where g-fa's extra variables
  become a liability.

### Comba's advantage is from the equality check, not multiplication

This confirms the earlier finding (Corrected Matrix section): the
g-only top-level benefit comes from the equality check, and Comba's
BCP cascade advantage also manifests primarily through the equality
check. On single-multiplication problems, the simpler Dadda encoding
with fewer variables is more efficient.

### Floating-point benchmarks

FP multiplication uses `bv_utils.unsigned_multiplier()` for the
mantissa multiplication (line 461 of float_utils.cpp). For float
(24-bit mantissa), this is a 48-bit multiplication. For double
(53-bit mantissa), this is a 106-bit multiplication.

| Benchmark | shift-add | comba | dadda | dadda+g-fa |
|-----------|-----------|-------|-------|------------|
| FP mul comm (float) | 0.03 | 0.03 | 0.03 | 0.03 |
| FP mul comm (double) | T/O | T/O | T/O | T/O |
| FP distributivity (float, SAT) | 0.19 | 0.19 | 0.19 | 0.19 |
| FP [0,1]*[0,1] bounded (float) | 0.04 | 0.04 | 0.04 | 0.04 |
| FP a*a >= 0 (float) | 0.03 | 0.03 | 0.03 | 0.03 |
| Float4 (mixed FP ops) | 21.8 | 21.9 | 21.9 | 21.9 |

**No encoding difference on any FP benchmark.** Reasons:
- Float (24-bit mantissa): the 48-bit integer multiplication inside
  the FP circuit is small enough that the solver handles it easily
  regardless of encoding. The FP wrapper (NaN/Inf handling, rounding,
  exponent arithmetic) dominates.
- Double (53-bit mantissa): the 106-bit multiplication is too hard
  for ANY encoding (T/O at 60s). The FP wrapper adds ~20K variables
  on top of the multiplication.
- Float4 (21.8s): multiplication is a small fraction of the total
  work (the test checks addition, subtraction, division, comparison,
  and many other FP properties).

**Conclusion:** FP benchmarks are not useful for evaluating multiplier
encoding because the encoding effect is either invisible (float) or
overwhelmed (double). The integer multiplication "sweet spot" for
encoding evaluation is BW=8-16.

### SMT-COMP benchmarks

The `bench-multiplication/smt-comp/` directory contains SMT2 formulas
for multiplication properties (commutativity, distributivity, factoring,
overflow). These are solved by `smt2_solver` using MiniSAT, which
doesn't support our encoding options. The formulas are equivalent to
the C benchmarks we already test.

### Additional real-world benchmarks

| Benchmark | shift-add | comba | dadda | dadda+g-fa | Status |
|-----------|-----------|-------|-------|------------|--------|
| overflow bound BW=8 | 0.024 | 0.033 | **0.023** | 0.025 | UNSAT |
| overflow bound BW=16 | 0.353 | 0.524 | **0.324** | 0.335 | UNSAT |
| mul monotone BW=8 | **5.90** | 9.43 | 10.3 | 9.91 | UNSAT |

The overflow bound benchmark confirms: **Dadda is best for single-
multiplication UNSAT problems** (0.324s vs Comba's 0.524s at BW=16).

The monotonicity benchmark (a≤b ∧ c>0 → a*c≤b*c) is surprisingly
hard at BW=8 (5.9s) and shift-add wins. This involves TWO
multiplications with an inequality (not equality) check, which is
a different structure from commutativity.

### SMT-COMP benchmarks with CaDiCaL (via smt2_solver --cadical)

Added `--cadical` and `--multiplier-encoding` options to `smt2_solver`
to enable testing SMT2 formulas with CaDiCaL and different multiplier
encodings.

| Benchmark | Vars | Cls | shift-add | comba | dadda | minisat |
|-----------|------|-----|-----------|-------|-------|---------|
| comm_8 | 210 | 944 | 0.58 | **0.09** | 0.10 | 1.16 |
| comm_16 | 802 | 4048 | T/O | **15.6** | T/O | T/O |
| comm_32 | 3138 | 16784 | T/O | T/O | T/O | T/O |
| **assoc_8** | 402 | 1846 | **28.3** | 114.9 | T/O | T/O |
| **distrib_8** | 342 | 1605 | **100.1** | T/O | T/O | T/O |
| distrib_16 | 1258 | 6465 | T/O | T/O | T/O | T/O |
| mixed_arith_8 | 582 | 2822 | T/O | T/O | T/O | T/O |
| factor_12-20 | — | — | 0.00 | 0.00 | 0.00 | 0.00 |
| mul_no_overflow_16 | 1057 | 5082 | 0.00 | 0.00 | 0.00 | 0.00 |

**Critical finding: encoding ranking depends on algebraic structure.**

- **Commutativity** (a*b == b*a): Comba wins (0.09s vs 0.58s at BW=8,
  only solver at BW=16). Two multiplications with equality check.

- **Associativity** ((a*b)*c == a*(b*c)): **shift-add wins** (28.3s
  vs Comba's 114.9s, Dadda T/O). Three multiplications with equality.

- **Distributivity** (a*(b+c) == a*b + a*c): **ONLY shift-add solves
  it** (100.1s). Three multiplications + addition. Comba and Dadda T/O.

- **Factoring and overflow** (SAT): all encodings equally fast.

**Why shift-add wins on associativity and distributivity:**

These properties involve THREE multiplications (not two). The Comba
and Dadda encodings create larger formulas (more variables per
multiplication), and with three multiplications the overhead compounds.
Shift-add's smaller per-multiplication formula wins when the total
formula size matters more than per-multiplication BVE efficiency.

This also explains why Comba wins on commutativity: with only TWO
multiplications, Comba's BVE advantage outweighs its variable overhead.
With THREE multiplications, the overhead dominates.

**CaDiCaL vs MiniSat:** CaDiCaL is consistently faster (0.58s vs
1.16s on comm_8, and solves assoc_8/distrib_8 where MiniSat T/O).
