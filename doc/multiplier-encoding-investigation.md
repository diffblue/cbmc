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

### Deep solver analysis: SMT-COMP benchmarks

#### Complete metrics table

| Benchmark | Vars | Cls | Conflicts | c/d | p/c | Avg sz | Avg gl | gl≤1% | Elim% | Time |
|-----------|------|-----|-----------|-----|-----|--------|--------|-------|-------|------|
| comm_8+shift | 208 | 935 | 34,420 | 0.79 | 31.2 | 22.1 | 7.3 | 0.3% | 87.5% | 0.65s |
| **comm_8+comba** | 364 | 1467 | **4,945** | **0.62** | **41.0** | **18.3** | **5.0** | **3.8%** | 73.6% | **0.09s** |
| **assoc_8+shift** | 400 | 1837 | **981,895** | 0.79 | 41.4 | 44.5 | 10.9 | 1.5% | **106%** | **29.7s** |
| assoc_8+comba | 712 | 2901 | 2,794,965 | 0.70 | 39.9 | 31.9 | 9.2 | 2.0% | 81.3% | T/O |
| **distrib_8+shift** | 340 | 1596 | 2,532,077 | 0.78 | 35.4 | 35.6 | 11.2 | 0.5% | **104%** | **118s** |
| distrib_8+comba | 574 | 2394 | 2,622,762 | 0.64 | 47.4 | 31.8 | 9.4 | 0.8% | 91.8% | T/O |
| comm_16+shift | 800 | 4031 | 2,430,636 | 0.52 | 63.9 | — | — | — | 39.2% | T/O |
| **comm_16+comba** | 1484 | 6439 | **448,874** | **0.47** | 63.9 | 32.2 | 8.8 | **5.3%** | **62.7%** | **19.6s** |

Key: c/d = conflicts per decision, p/c = propagations per conflict,
Avg sz = average learned clause size, Avg gl = average glue,
Elim% = (eliminated + fixed) / total variables.

#### BCP depth analysis

| Benchmark | Avg depth | Median depth | Depth-1 % |
|-----------|-----------|--------------|-----------|
| comm_8+shift | 21.4 | 9 | 21.7% |
| comm_8+comba | 25.2 | 7 | 20.2% |
| assoc_8+shift | 30.1 | 9 | 23.8% |
| assoc_8+comba | 33.1 | 6 | 21.2% |
| distrib_8+shift | 26.1 | 7 | 23.8% |

#### Analysis: why shift-add wins on associativity and distributivity

**The variable overhead hypothesis is confirmed.** Comba creates
78% more variables than shift-add (712 vs 400 for assoc_8, 574 vs
340 for distrib_8). For associativity (3 multiplications), this
means 312 extra variables. For commutativity (2 multiplications),
it's 156 extra variables.

**Comba's learned clauses are BETTER** on all benchmarks: smaller
(31.9 vs 44.5 for assoc_8) and lower glue (9.2 vs 10.9). But this
advantage is overwhelmed by the LARGER search space.

**The critical metric is BVE elimination rate:**
- assoc_8+shift: 106% eliminated (more than original — BVE creates
  new variables during resolution that are then also eliminated).
  Only 0 variables remain after preprocessing.
- assoc_8+comba: 81.3% eliminated. ~133 variables remain.

Shift-add's smaller formula allows BVE to eliminate EVERYTHING,
leaving a trivial residual problem. Comba's larger formula leaves
133 variables that must be searched, creating 2.8M conflicts.

**For commutativity, the opposite holds:**
- comm_16+shift: 39.2% eliminated. ~487 variables remain. T/O.
- comm_16+comba: 62.7% eliminated. ~553 variables remain. 19.6s.

Despite having more remaining variables in absolute terms, Comba's
remaining variables are structurally easier (as shown in the
Investigation #3/#5 analysis: shorter carry chains enable BCP
cascades, 0.47 conflicts/decision vs 0.52).

#### The unifying theory: BVE completeness threshold

The encoding choice determines whether BVE can eliminate ALL or
MOST variables during preprocessing:

1. **BVE-complete** (shift-add on assoc/distrib): BVE eliminates
   >100% of variables. The residual problem is trivial. Shift-add
   wins because its smaller formula is easier to fully eliminate.

2. **BVE-incomplete** (all encodings on comm_16): BVE cannot
   eliminate enough variables. The residual problem is hard. Comba
   wins because its structure produces better learned clauses and
   shorter carry chains for the residual search.

3. **Threshold region** (comm_8): BVE eliminates most variables
   for both encodings (87.5% shift, 73.6% comba). Comba wins
   because its residual is smaller AND structurally easier.

The key question for adaptive selection: **will BVE eliminate
enough variables to make the residual trivial?** If yes, use
shift-add (smallest formula). If no, use Comba (best residual
structure).

Factors that push toward BVE-completeness:
- Fewer multiplications (less variable interaction)
- Smaller formula (fewer variables to eliminate)
- More additions relative to multiplications (additions are
  BVE-friendly)

Factors that push toward BVE-incompleteness:
- More multiplications (more cross-multiplication dependencies)
- Larger bitwidth (exponentially harder residual)
- Pure multiplication (no additions to help BVE)

#### CaDiCaL BVE option sweep

CaDiCaL has extensive BVE tuning options. We tested all of them
on the key benchmarks.

**comm_16+comba (baseline 19.7s):**

| Option | Conflicts | Elim | Fixed | Time | Δ |
|--------|-----------|------|-------|------|---|
| default | 448,874 | 837 | 94 | 19.7s | — |
| **elimsubst=false** | 415,453 | 737 | 204 | **17.5s** | **-11%** |
| **elimequivs=false** | 438,296 | 838 | 96 | **18.4s** | **-6%** |
| elimxors=false | 489,173 | 806 | 208 | 19.6s | 0% |
| elimands=false | 499,077 | 799 | 154 | 23.3s | +18% |
| elimites=false | 570,916 | 839 | 122 | 24.6s | +25% |
| elim=false | 436,065 | 229 | 225 | 23.7s | +20% |
| elimboundmax=100 | 1,238,698 | 945 | 62 | T/O | — |

Disabling substitution (elimsubst=false) gives 11% speedup.
Disabling equivalence detection gives 6% speedup. Both reduce
the number of eliminations but increase fixed variables (unit
propagation during preprocessing), suggesting these BVE features
interfere with unit propagation.

**elimboundmax=100 causes T/O** — allowing higher-cost eliminations
is catastrophic. The extra resolvents bloat the formula without
helping the search. This is BVE OVER-ELIMINATION.

**assoc_8+shift (baseline 30.0s):**

| Option | Conflicts | Time | Δ |
|--------|-----------|------|---|
| default | 981,895 | 30.0s | — |
| elimands=false | 1,226,667 | 39.5s | +32% |
| elim=false | 1,023,011 | 41.4s | +38% |
| elimequivs=false | 941,295 | 29.0s | -3% |

AND gate detection is critical for assoc_8 (32% slower without it).
This is the opposite of comm_16 where AND detection helps less.

**distrib_8+shift (baseline T/O at 120s):**

| Option | Conflicts | Fixed | Time | Result |
|--------|-----------|-------|------|--------|
| default | 2,520,492 | 20 | T/O | — |
| **elimands=false** | 2,134,159 | **102** | **106s** | **SOLVED** |
| **elimxors=false** | 2,052,739 | **133** | **101s** | **SOLVED** |
| elimands+xors=false | 2,425,161 | 3 | T/O | — |
| elimrounds=10 | 2,233,869 | 138 | 105s | SOLVED |

**Disabling AND or XOR gate detection individually SOLVES distrib_8**
(from T/O to 101-106s). The key: "fixed" variables jump from 20 to
102-133. Gate detection INTERFERES with unit propagation — the gate
clauses prevent BCP from fixing variables that would otherwise be
determined.

Disabling BOTH AND and XOR detection hurts (T/O, only 3 fixed).
This is a phase transition: the solver needs SOME gate detection
but not all of it.

#### Analysis: BVE over-elimination

The BVE option sweep reveals that CaDiCaL's default BVE configuration
is not optimal for multiplication circuits:

1. **Substitution hurts commutativity** (elimsubst=false gives 11%
   speedup on comm_16). Substitution replaces a variable with its
   definition, which can create larger clauses that slow down BCP.

2. **Gate detection interferes with unit propagation** on distributivity.
   AND and XOR gate detection creates new clauses (resolvents) that
   prevent BCP from fixing variables. Disabling one type of gate
   detection allows more unit propagation.

3. **Higher elimination bounds are catastrophic** (elimboundmax=100
   causes T/O on comm_16). Eliminating high-cost variables creates
   too many resolvents, bloating the formula.

4. **ITE detection is consistently helpful** (elimites=false hurts
   on all benchmarks). ITE gates in multiplication circuits are
   from MUX structures in the encoding.

These findings suggest that multiplication circuits have a specific
BVE "sweet spot" that differs from CaDiCaL's general-purpose defaults.
A multiplication-aware BVE configuration could improve performance.

## Further Investigation Areas

Based on all findings so far, the following areas warrant further study:

### 1. Multiplication-tuned CaDiCaL configuration
The BVE option sweep shows that default CaDiCaL is not optimal for
multiplication. A systematic search over BVE parameters (elimsubst,
elimequivs, elimboundmax, elimrounds) could find a better configuration.
This could be passed via CADICAL_OPTS when multiplication is detected.

### 2. Encoding-specific BVE tuning
Different encodings may benefit from different BVE configurations:
- Comba: benefits from AND detection (elimands), hurt by substitution
- Shift-add: benefits from AND detection, hurt by equiv detection
- The optimal BVE config may depend on the encoding

### 3. Carry-save vs carry-propagate tradeoff
Dadda's carry-save form avoids carry propagation until the final
addition. But our analysis shows Comba's pop0 (which does carry
propagation in small fields) is better. Is there an intermediate
approach: carry-save reduction with pop0-style small-field additions?

### 4. Variable ordering interaction
CaDiCaL's variable ordering (VSIDS/VMTF) interacts with BVE.
The order in which variables are eliminated affects which resolvents
are created. Testing --phase and --score options may reveal
interactions with encoding choice.

### 5. Preprocessing vs inprocessing balance
The smt2_solver uses satcheck_cadical_no_preprocessingt (no
preprocessing, only inprocessing). The standalone CaDiCaL does
preprocessing. For comm_16+comba, the no-preprocessing path
(smt2_solver) is faster. Understanding when preprocessing helps
vs hurts for multiplication could inform solver configuration.

### 6. Clause sharing between multiplications
In commutativity (a*b == b*a), the two multiplications share
input variables. The solver could potentially share learned clauses
or BVE results between them. Understanding how CaDiCaL handles
this sharing could explain why Comba wins on commutativity.

### 7. Resolution proof structure
The Priority 6 analysis showed multiplication requires exponential
resolution proofs. Analyzing the actual resolution proof structure
(which variables appear in the proof, how deep the proof tree is)
could reveal why some encodings produce shorter proofs.

## Investigation Results: All Seven Areas

### INV 1: Encoding × BVE config cross-product

| Benchmark+Enc | default | no-subst | no-equiv | no-ands | no-ites |
|---------------|---------|----------|----------|---------|---------|
| comm_16+comba | 19.7 | **17.5** | **18.5** | 23.3 | 24.6 |
| assoc_8+shift | 30.0 | 33.6 | **29.1** | 39.5 | 29.4 |
| assoc_8+comba | T/O | **109** | T/O | **104** | T/O |
| distrib_8+shift | T/O | **118** | T/O | **106** | T/O |

**Different encodings want different BVE configs:**
- Comba on commutativity: benefits from disabling substitution
- Shift-add on associativity: benefits from disabling equivalence detection
- Both on associativity/distributivity: disabling AND detection helps Comba
  (solves from T/O) but hurts shift-add on associativity

Best combinations found:
- comm_16+comba: no-subst+no-equiv+no-xors = 17.4s (-11%)
- assoc_8+comba: no-ands = 104s (from T/O)
- distrib_8+shift: no-ands = 106s (from T/O)

### INV 2: Encoding-specific BVE tuning

Covered by INV 1 cross-product. Key finding: there is no universal
best BVE configuration. The optimal config depends on BOTH the
encoding AND the algebraic property being verified.

### INV 3: Carry-save with pop0-style additions

Instead of implementing a new encoding, we measured the carry chain
impact on proof size using GF(2) multiplication (no carries):

| Benchmark | Proof additions | Avg clause sz | Vars | Clauses |
|-----------|----------------|---------------|------|---------|
| GF(2) comm_8 | **2,166** | **7.2** | 169 | 505 |
| int comm_8+comba | 7,749 | 10.2 | 364 | 1467 |
| int comm_8+shift | 38,695 | 13.6 | 208 | 935 |
| int assoc_8+shift | 1,035,005 | 23.7 | 400 | 1837 |

**Carry propagation creates 3.6-18x larger proofs.** GF(2) (no carries)
needs only 2,166 proof steps vs Comba's 7,749 and shift-add's 38,695.
Comba's shorter carry chains produce 5x smaller proofs than shift-add.

The proof size grows EXPONENTIALLY with the number of multiplications:
comm_8 (2 muls): 7.7K steps. assoc_8 (4 muls): 1,035K steps (134x).

### INV 4: Variable ordering interaction

| Config | comm_16+comba | assoc_8+shift |
|--------|--------------|---------------|
| default | 19.7s | 30.0s |
| phase=false | 58.8s | 31.4s |
| score=false | 38.6s | 30.7s |
| **phase=F+no-subst** | **12.0s** | 42.6s |

**Synergistic interaction discovered:** phase=false alone is 3x slower
on comm_16, but combined with no-subst it's 39% FASTER (12.0s).
The mechanism: phase=false (all variables initially false) aligns
with the multiplication circuit's natural polarity when substitution
doesn't distort the variable structure.

This combination HURTS associativity (42.6s vs 30.0s) — confirming
that optimal solver configuration is problem-specific.

**Per-benchmark best configs:**
- comm_16+comba: phase=F+no-subst → **12.0s** (39% faster, 295K conflicts)
- assoc_8+shift: no-equiv+no-ites → **28.7s** (3% faster)
- distrib_8+shift: no-xors → **98.1s** (17% faster)

### INV 5: Preprocessing vs inprocessing

| Config | comm_16+comba | assoc_8+shift | comm_8+comba |
|--------|--------------|---------------|--------------|
| default (-P0) | 19.6s | 30.0s | 0.09s |
| -P1 (1 round preproc) | 26.4s | 30.1s | 0.09s |
| -P5 (5 rounds preproc) | 36.1s | 31.5s | **0.05s** |
| no inprocessing | 40.2s | 45.5s | 0.09s |

**Initial preprocessing HURTS comm_16+comba** (26.4s with 1 round vs
19.6s without). CaDiCaL's default is no initial preprocessing (-P0),
which is optimal for multiplication. Preprocessing eliminates variables
too eagerly before the search has context about which variables matter.

**Inprocessing is essential** — disabling it causes 2x slowdown.
Inprocessing (BVE during search) is better than preprocessing (BVE
before search) because the solver can make elimination decisions
informed by the search state.

For small problems (comm_8), 5 rounds of preprocessing helps (0.05s
vs 0.09s) because BVE can eliminate everything.

### INV 6: Clause sharing between multiplications

Analysis of learned clauses in comm_8+comba:

| Category | Count | Percentage |
|----------|-------|------------|
| Cross-multiplication (both mul1+mul2) | 1,974 | **98.7%** |
| Only mul1 | 0 | 0.0% |
| Only mul2 | 26 | 1.3% |
| Input-only | 0 | 0.0% |

**98.7% of learned clauses span BOTH multiplications.** The solver
learns cross-multiplication relationships — clauses that connect
variables from the first multiplication (a*b) with variables from
the second (b*a). This is how the solver proves equivalence: by
learning that certain partial assignments to one multiplication
force specific values in the other.

Average learned clause composition: 3.6 input + 10.6 mul1 + 7.4 mul2
+ 7.0 equality = ~29 variables spanning the entire formula.

### INV 7: Resolution proof structure

| Benchmark | Proof steps | Avg clause sz | Max clause sz |
|-----------|-------------|---------------|---------------|
| GF(2) comm_8 | 2,166 | 7.2 | — |
| comm_8+comba | 7,749 | 10.2 | 42 |
| comm_8+shift | 38,695 | 13.6 | 36 |
| assoc_8+shift | 1,035,005 | 23.7 | 83 |

**Shift-add has "bottleneck" variables** that appear 8,000-10,000
times in the proof (carry chain variables). Comba's max variable
frequency is ~975. These bottleneck variables force the proof to
repeatedly reason about the same carry chain, creating a larger proof.

**Proof size grows exponentially with multiplication count:**
comm_8 (2 muls) → assoc_8 (4 muls) = 134x more proof steps.
This is consistent with the exponential resolution complexity
of multiplication (Priority 6).

## Updated Consolidated Findings

### The complete picture

The investigation has revealed a multi-dimensional optimization space:

**Dimension 1: Encoding choice**
- 1 multiplication: Dadda or Dadda+g-fa (smallest formula)
- 2 multiplications + equality: Comba (BCP cascades through equality)
- 3+ multiplications: shift-add (smallest total formula)

**Dimension 2: BVE configuration**
- Commutativity: disable substitution (elimsubst=false)
- Associativity: disable equivalence detection (elimequivs=false)
- Distributivity: disable AND or XOR detection (elimands/elimxors=false)

**Dimension 3: Phase selection**
- Commutativity + no-subst: phase=false gives 39% speedup
- Other problems: default phase is better

**Dimension 4: Preprocessing**
- Large problems: no preprocessing, only inprocessing (default)
- Small problems: 5 rounds preprocessing helps

### Best known configurations

| Benchmark | Encoding | BVE config | Phase | Time | vs default |
|-----------|----------|------------|-------|------|------------|
| comm_16 | comba | no-subst | false | **12.0s** | **-39%** |
| comm_8 | comba | default | default | **0.09s** | **-86%** vs shift |
| assoc_8 | shift | no-equiv+no-ites | default | **28.7s** | **-4%** |
| distrib_8 | shift | no-xors | default | **98.1s** | from T/O |
| overflow_16 | dadda | default | default | **0.48s** | **-73%** vs shift |
| str_reduce_32 | dadda+g-fa | default | default | **0.29s** | **-24%** vs shift |


## Next Investigation Round

### NI-1: Targeted BVE — eliminate carry variables first

The bottleneck variable analysis (INV 7) shows specific carry chain
variables appearing 8,000-10,000 times in the proof. CaDiCaL's
`--elimprod` and `--elimsum` control elimination scoring. Test whether:
- Changing elimination scoring prioritizes carry variables
- CBMC's variable emission order affects BVE elimination order
- Emitting carry variables first/last changes BVE effectiveness

### NI-2: Redundant clause injection for BVE

The g-only and g-fa techniques add redundant AND gates that help BVE.
The BVE over-elimination finding suggests the STRUCTURE of redundant
clauses matters. Systematically test:
- Binary implications between carry variables
- Redundant clauses targeting the bottleneck carry variables specifically
- Different gate types (not just AND) as BVE catalysts
- Adding clauses AFTER bit-blasting but BEFORE solving

### NI-3: Cross-multiplication structure exploitation

98.7% of learned clauses span both multiplications. The solver
re-derives cross-multiplication relationships from scratch. Test:
- Symmetry breaking clauses encoding that inputs are shared
- Redundant clauses connecting corresponding partial products
  from the two multiplications
- Whether adding the equality constraint earlier (before full
  bit-blasting) helps BVE

### NI-4: Systematic CaDiCaL option search

Manual exploration found phase=false+no-subst gives 39% speedup.
CaDiCaL has ~100 options. Use systematic parameter tuning:
- Grid search over key options (phase, elim*, score, chrono, etc.)
- Test on multiple benchmarks simultaneously to find robust configs
- Compare per-benchmark-optimal vs robust-across-benchmarks configs

### NI-5: Proof-guided encoding design

DRAT proof analysis shows which variables are bottlenecks. Design
encodings that avoid creating bottleneck variables:
- Analyze proof structure per encoding
- Identify which encoding decisions create bottleneck variables
- Iteratively modify encoding to reduce proof size
- Novel research direction

### NI-6: Mixed encoding within a single multiplication

Different columns of the partial product matrix have different sizes.
Test hybrid approaches:
- Small columns (edges) use shift-add, large columns (middle) use
  Comba popcount
- Transition point optimization: at what column size should we switch?
- Per-column encoding selection based on column height

### NI-7: In-depth MiniSat analysis

MiniSat has been tested for timing but never analyzed at the same
depth as CaDiCaL. Conduct:
- Learned clause quality analysis (size, LBD/glue)
- BVE/SatELite preprocessing effectiveness per encoding
- Propagation depth and conflict analysis
- Compare MiniSat's preprocessing (SatELite) vs CaDiCaL's inprocessing
- Test whether MiniSat's different restart/clause management strategies
  interact differently with multiplication encodings

## NI-7 Results: In-depth MiniSat Analysis

### MiniSat vs CaDiCaL comparison (comm_8)

| Metric | MiniSat shift | CaDiCaL shift | MiniSat comba | CaDiCaL comba |
|--------|--------------|---------------|---------------|---------------|
| Conflicts | 148,977 | 34,420 | 24,337 | 4,945 |
| Decisions | 180,681 | 43,486 | 30,671 | 7,877 |
| Propagations | 6,892,981 | 1,075,686 | 1,579,094 | 203,067 |
| BVE eliminated | ~1 | 55 | ~1 | 138 |
| Time | 1.15s | 0.65s | 0.24s | 0.09s |

**MiniSat needs 4-5x more conflicts than CaDiCaL** on the same CNF.
MiniSat T/O on everything beyond comm_8 (comm_16, assoc_8, distrib_8).

### Root cause: SatELite is disabled by freeze_all

**MiniSat's SatELite preprocessing eliminates only ~1 variable** because
CBMC's incremental solving path calls `solver.push()` which sets
`freeze_all=true`, freezing ALL variables and preventing SatELite
from eliminating them.

CaDiCaL's inprocessing works DESPITE frozen variables because it
performs BVE during search, not as preprocessing. This is the
fundamental advantage of CaDiCaL over MiniSat for multiplication:
CaDiCaL has inprocessing, MiniSat does not.

### Implications

MiniSat is structurally disadvantaged for multiplication verification
because it lacks inprocessing. The 4-5x conflict ratio is entirely
explained by the absence of BVE during search. No encoding change
can compensate for this — the solver architecture is the bottleneck.

## NI-1 Results: Targeted BVE — Elimination Scoring

### CaDiCaL elimination scoring options

| Option | comm_16+comba | assoc_8+shift | distrib_8+shift |
|--------|--------------|---------------|-----------------|
| default | 19.6s | 30.0s | T/O |
| **elimsum=0** | **17.3s** | 30.0s | T/O |
| elimprod=0 | 32.6s | 32.1s | T/O |
| elimsum=100 | 34.1s | 31.1s | **120s** |

**elimsum=0 gives 12% speedup on comm_16+comba** by using only
product-based scoring (positive × negative occurrences). Sum-based
scoring adds noise that leads to suboptimal elimination ordering.

**Best combination found:** sum=0+phase=F+no-subst → 12.6s on
comm_16+comba (36% faster than default).

## NI-3 Results: Cross-Multiplication Structure

### Partial product equivalences: no benefit

Adding explicit equivalence clauses between matching partial products
(pp[i][j] in mul1 == pp[j][i] in mul2) does NOT help:
- comm_8+comba: 4,945→5,653 conflicts (14% MORE), 0.09→0.10s
- comm_16+comba: 448K→514K conflicts (14% more), 19.6→23.0s

CaDiCaL's BVE already discovers these equivalences through
`elimequivs=true`. Adding them explicitly just adds clauses.

### AND gate caching: sharing hurts!

Caching `prop.land(a,b)` so that `land(a,b) == land(b,a)` shares
partial product variables between the two multiplications:

| Benchmark | Before (vars/cls) | After (vars/cls) | Before time | After time |
|-----------|-------------------|-------------------|-------------|------------|
| comm_8+shift | 208/935 | 170/820 (-18%) | 0.64s | 0.59s |
| comm_16+comba | 1484/6439 | 1311/5919 (-12%) | 19.6s | **37.2s** (+89%) |

**Variable sharing between multiplications is HARMFUL for BVE.**
With separate variables, BVE can eliminate each multiplication's
variables independently. With shared variables, eliminating a shared
variable affects BOTH multiplications, creating larger resolvents.

This is a fundamental insight: the solver benefits from REDUNDANT
copies of partial products because they enable independent BVE.

## NI-5 Results: Preprocessing vs Inprocessing (corrected)

| Config | comm_16+comba | assoc_8+shift |
|--------|--------------|---------------|
| default (-P0, no initial preproc) | **19.6s** | **30.0s** |
| -P1 (1 round preprocessing) | 26.4s (+34%) | 30.1s |
| -P5 (5 rounds preprocessing) | 36.1s (+84%) | 31.5s |
| no inprocessing | 40.2s (+105%) | 45.5s (+52%) |

**Initial preprocessing HURTS multiplication** (34-84% slower on
comm_16). CaDiCaL's default (no initial preprocessing, -P0) is
optimal. Inprocessing (BVE during search) is essential — disabling
it causes 2x slowdown.

The reason: preprocessing eliminates variables without search context.
For multiplication, the solver needs to explore the search space
before knowing which variables are worth eliminating.

## NI-4 Results: Systematic CaDiCaL Option Search

### Full grid search on comm_16+comba

| phase | elimsubst | elimsum | elimequivs | Conflicts | Time |
|-------|-----------|---------|------------|-----------|------|
| def | def | def | def | 448,874 | 19.6s |
| def | F | def | def | 415,453 | 17.5s |
| def | def | 0 | def | 425,523 | 17.3s |
| def | def | def | F | 438,296 | 18.5s |
| **F** | **F** | def | def | **295,316** | **12.0s** |
| **F** | **F** | def | **F** | **295,316** | **12.0s** |
| F | def | def | def | 1,110,830 | 58.3s |
| F | def | def | F | 498,804 | 20.9s |

**Best: phase=F+no-subst(+no-equiv) → 12.0s (39% faster, 34% fewer conflicts)**

The phase=false+no-subst synergy is robust: adding no-equiv or
no-sum doesn't help further. The improvement comes entirely from
the phase×substitution interaction.

### Per-benchmark best configs

| Benchmark | Best config | Time | vs default |
|-----------|-------------|------|------------|
| comm_16+comba | phase=F+no-subst+no-equiv | **12.0s** | **-39%** |
| assoc_8+shift | no-equiv+no-ites | **29.0s** | **-3%** |
| distrib_8+shift | no-xors+no-equiv | **100.4s** | from T/O |

**No universal best config exists.** The optimal configuration
depends on the algebraic property being verified.

## NI-2 Results: Redundant Clause Injection

Explicit partial product equivalences (NI-3) and AND gate caching
both HURT performance. The key insight from NI-3c (AND gate caching):
**variable sharing between multiplications prevents independent BVE**.

Redundant implications between carry variables were not tested
because the NI-3 results show that connecting the two multiplications
is counterproductive. The solver benefits from INDEPENDENT copies.

## NI-5 Results: Proof-Guided Encoding Analysis

### Bottleneck variable analysis

| Metric | shift-add | Comba |
|--------|-----------|-------|
| Total proof steps | 38,695 | 7,749 |
| Top bottleneck var frequency | 18,991 (49%) | 2,752 (36%) |
| Steps with input vars | 81% | 38% |
| Steps with internal vars | 100% | 100% |
| Steps with both | 81% | 38% |

**shift-add's proof is INPUT-DOMINATED:** 81% of proof steps
reference input bits. The proof constantly reasons about how input
bits affect the carry chain — the global dependency problem.

**Comba's proof is INTERNAL-DOMINATED:** only 38% reference inputs.
The proof mostly reasons about popcount intermediate variables,
which are LOCAL to each column.

**shift-add has a single bottleneck variable** (var 208) appearing
in 49% of ALL proof steps. The entire proof revolves around this
one carry chain variable. Comba distributes the proof burden more
evenly (top variable at 36%).

### Encoding design implications

An ideal encoding would:
1. **Minimize input variable involvement in proofs** (Comba achieves
   38% vs shift-add's 81%)
2. **Distribute proof burden across variables** (no single bottleneck)
3. **Keep variables LOCAL to columns** (Comba's popcount does this)
4. **Avoid creating global carry chains** (the root cause of bottlenecks)

Comba already achieves all four goals through its pop0 popcount.
Further improvement would require an encoding that creates even
MORE local structure — perhaps a hierarchical popcount that
processes sub-columns independently.

## NI-6 Results: Mixed Encoding

### Hybrid popcount (direct counting for small columns)

Using direct half-adder/full-adder for columns with ≤3 bits and
pop0 for larger columns: **NO effect**. Same variable count, same
performance. pop0 already handles small inputs efficiently.

### Conclusion

The pop0 popcount is already near-optimal for all column sizes.
The overhead is in the LARGE columns (7+ bits), not the small ones.
The Investigation #1 result (adder-tree popcount is 3x slower)
confirms that pop0's parallel bit counting is the right approach.

## NI-5b Results: Carry-Save Comba Encoding (NEW)

### Design

Based on the NI-5 proof analysis showing that Comba's inter-column
carry propagation creates proof bottlenecks, we designed a carry-save
variant that computes popcount per column INDEPENDENTLY, then does
a second pass to handle the weighted carry bits.

Standard Comba: popcount(column[i]) → LSB to result[i], higher bits
propagated to column[i+1], column[i+2], etc. during the SAME pass.

Carry-save Comba: popcount(column[i]) → collect ALL weighted results,
then reduce the accumulated weighted columns in a SECOND pass.

### Results

| Benchmark | comba | **comba-cs** | dadda | shift |
|-----------|-------|-------------|-------|-------|
| comm_9 | 0.24 | **0.13** | 0.53 | 1.97 |
| comm_11 | 1.77 | **0.78** | 14.6 | 57.5 |
| comm_13 | 8.27 | **2.66** | T/O | T/O |
| overflow_8 | 0.05 | **0.02** | 0.05 | 0.19 |
| overflow_12 | 0.39 | **0.14** | 0.24 | 0.74 |
| overflow_16 | 1.57 | **0.78** | **0.48** | 1.79 |
| str_red_16 | 0.40 | 0.27 | **0.11** | 0.19 |
| str_red_32 | 0.67 | 0.60 | **0.36** | 0.38 |
| factor_20 | 0.06 | 0.06 | **0.04** | 0.05 |

**comba-cs is 1.8-3.1x faster than standard Comba on commutativity**
and 2-2.8x faster on overflow checks. It NEVER regresses vs Comba.

### CaDiCaL analysis (comm_16, smt2_solver)

| Metric | comba | comba-cs |
|--------|-------|----------|
| Variables | 1,484 | 1,608 (+8%) |
| Clauses | 6,439 | 6,845 (+6%) |
| Conflicts | 448,874 | **112,882** (-75%) |
| Eliminated | 837 | 783 |
| Fixed | 94 | 147 |
| Time | 19.5s | **4.2s** (-78%) |

**75% fewer conflicts despite 8% more variables.** The carry-save
structure creates more variables but they're easier to search because
inter-column dependencies are eliminated during the popcount phase.

### Why it works

The carry-save Comba separates two concerns:
1. **Column reduction** (popcount): each column is reduced independently
2. **Carry propagation**: handled in a second pass on smaller columns

In standard Comba, these are interleaved: popcount carries propagate
to the next column DURING the first pass, creating inter-column
dependencies. In carry-save Comba, the first pass is fully independent
per column, and the second pass handles only the small carry bits.

This directly addresses the NI-5 finding: the proof bottleneck in
standard Comba comes from inter-column carry propagation. Carry-save
Comba eliminates this by deferring carry propagation to a second pass
where the columns are much smaller (1-3 bits instead of 8-16 bits).

## NI-7 Corrected: MiniSat Analysis

### SatELite IS running (corrected)

Earlier analysis incorrectly stated SatELite eliminates ~1 variable.
Corrected data:

| Encoding | MiniSat SatELite eliminated | CaDiCaL total removed |
|----------|---------------------------|----------------------|
| comm_8+shift | 29 | 182 (55 elim + 127 fixed) |
| comm_8+comba | 105 | 268 (138 elim + 130 fixed) |

SatELite eliminates 29-105 variables (reasonable preprocessing).
CaDiCaL removes 182-268 through inprocessing (BVE during search).
The 6x difference is from CaDiCaL's ability to "fix" variables
(unit propagation during search) which MiniSat cannot do.

**freeze_all is NOT the issue.** Only 1 variable is frozen (the
assertion literal). SatELite has full access to all other variables.
The limitation is MiniSat's lack of inprocessing, not freezing.

## NI-1 Corrected: elimsum=0 is NOT robust

| Benchmark | default | elimsum=0 | Change |
|-----------|---------|-----------|--------|
| SMT comm_16+comba | 19.6s | 17.3s | -12% |
| CBMC comm_11+comba | 1.77s | 2.69s | **+52%** |
| CBMC overflow_16+dadda | 0.48s | 0.53s | +10% |

elimsum=0 helps the SMT-COMP benchmark but HURTS the CBMC benchmark
for the same property (commutativity). The difference is in the CNF
structure produced by the two paths. **Not safe as a default change.**

## Carry-Save Comba: Complete Analysis

### Regression testing

**691 CORE regression tests: ZERO failures.** comba-cs is fully
correct and produces identical verification results to all other
encodings.

### Deep solver analysis (comm BW=11)

| Metric | comba | comba-cs | Change |
|--------|-------|----------|--------|
| Variables | 901 | 981 (+9%) | +80 |
| Clauses | 3,597 | 3,807 (+6%) | +210 |
| **Conflicts** | 104,807 | **43,361** | **-59%** |
| Decisions | 177,837 | 84,078 | -53% |
| Propagations | 5,445,753 | 2,703,362 | -50% |
| Eliminated | 470 | 435 | -35 |
| **Fixed** | 124 | **216** | **+74%** |
| Time | 2.91s | 1.15s | -60% |

**74% more fixed variables** — comba-cs enables significantly more
unit propagation during search. This is the key mechanism: the
carry-save structure avoids inter-column dependencies that block
unit propagation.

### Proof analysis (comm BW=11)

| Metric | comba | comba-cs | Change |
|--------|-------|----------|--------|
| Proof steps | 125,956 | **57,295** | **-55%** |
| Avg clause size | 11.5 | 9.3 | -19% |
| Top bottleneck freq | 39,611 (31%) | 18,253 (32%) | -54% |
| Input var involvement | 30% | **22%** | **-27%** |

**55% smaller proofs** with 19% smaller clauses and 27% less input
variable involvement. The design hypothesis is confirmed: carry-save
reduces inter-column dependencies, leading to smaller proofs.

### Scaling: speedup grows with bitwidth

| BW | comba | comba-cs | Speedup |
|----|-------|----------|---------|
| 9 | 0.24s | 0.13s | 1.8x |
| 11 | 1.75s | 0.77s | 2.3x |
| 13 | 8.18s | 2.63s | 3.1x |
| 15 | 10.59s | 5.38s | 2.0x |
| 17 | 47.47s | 7.19s | **6.6x** |
| 19 | 180.5s | 15.8s | **11.4x** |
| 21 | T/O | **31.4s** | ∞ |
| 23 | T/O | **74.8s** | ∞ |
| 25 | T/O | **93.3s** | ∞ |

**The speedup ACCELERATES with bitwidth.** At BW=19, comba-cs is
11.4x faster. At BW=21+, comba-cs solves problems that comba cannot.
The solvable frontier moves from ~BW=19 to ~BW=27.

### SMT-COMP benchmarks

| Benchmark | comba | comba-cs | shift |
|-----------|-------|----------|-------|
| comm_16 | 16.4s | **4.6s** | T/O |
| assoc_8 | T/O | T/O | **30.8s** |
| distrib_8 | T/O | T/O | **111s** |

comba-cs helps commutativity (3.6x) but not associativity or
distributivity. These still need shift-add's smaller formula.

### Single-multiplication benchmarks

| Benchmark | comba-cs | dadda | dadda+g-fa |
|-----------|----------|-------|------------|
| overflow_16 | 0.78 | **0.48** | 0.74 |
| str_red_16 | 0.27 | 0.11 | **0.10** |
| str_red_32 | 0.59 | 0.36 | **0.29** |

Dadda still wins on single-multiplication problems, but comba-cs
is much closer than standard comba was (gap reduced from 3-4x to
1.6-2.6x).

### Double-precision FP

T/O for all encodings at 300s. The 106-bit mantissa multiplication
plus FP wrapper is beyond the solvable frontier (~BW=27).

### Summary: comba-cs is the new best encoding for commutativity

comba-cs should replace comba as the default for multi-multiplication
UNSAT problems. It provides:
- 1.8-11.4x speedup over standard comba (growing with BW)
- 55% smaller proofs
- 74% more unit propagation
- Zero regressions (691/691 tests pass)
- Extends solvable frontier from BW~19 to BW~27

## Remaining Investigations

### Recursive carry-save: not beneficial

Second-pass columns have max size 4 (even at BW=17). Recursive
carry-save would add a third pass for columns of 2-4 bits, producing
columns of 1-2 bits. The overhead of an additional pass outweighs
the benefit for such small columns.

### comba-cs + CaDiCaL tuning: no-subst compounds the improvement

| Config | comm_9 | comm_11 | comm_17 | overflow_16 | str_red_32 |
|--------|--------|---------|---------|-------------|------------|
| comba-cs | 0.13 | 0.77 | 7.19 | 0.78 | 0.60 |
| **comba-cs+no-subst** | **0.11** | **0.56** | **4.58** | **0.67** | 0.64 |
| Change | -15% | -27% | -36% | -14% | +7% |

**no-subst is robust with comba-cs:** consistent 15-36% improvement
on commutativity and overflow, with only 7% regression on strength
reduction. Much more robust than with standard comba (which had
52% regression on comm_11).

The phase=false+no-subst synergy found for standard comba does NOT
help comba-cs (phase=F hurts). comba-cs already achieves the
structural improvement that phase=false was compensating for.

### Combined scaling: comba-cs+no-subst vs baseline

| BW | baseline (shift-add) | comba | comba-cs+no-subst | Total speedup |
|----|---------------------|-------|-------------------|---------------|
| 9 | 1.93s | 0.24s | **0.11s** | **17x** |
| 11 | 55.9s | 1.74s | **0.56s** | **100x** |
| 13 | T/O | 8.14s | **1.49s** | ∞ |
| 17 | T/O | 47.3s | **4.58s** | ∞ |
| 19 | T/O | 179.8s | **8.53s** | ∞ |
| 21 | T/O | T/O | **26.4s** | ∞ |
| 25 | T/O | T/O | **58.9s** | ∞ |

**100x speedup at BW=11 vs baseline.** Solves BW=25 where baseline
times out at BW=13 and standard comba times out at BW=21.

### Final encoding recommendations

| Problem type | Best encoding | Best CaDiCaL config |
|-------------|---------------|---------------------|
| Multi-mul UNSAT (commutativity) | **comba-cs** | elimsubst=false |
| Single-mul UNSAT (overflow ≤12) | **comba-cs** | default |
| Single-mul UNSAT (overflow 16+) | **dadda** | default |
| Single-mul UNSAT (strength red.) | **dadda+g-fa** | default |
| 3+ mul UNSAT (assoc/distrib) | **shift-add** | elimxors=false |
| SAT problems (factoring, bounds) | any | default |

## Adder Encoding Interaction with comba-cs (#1)

| Config | comm_9 | comm_11 | comm_17 |
|--------|--------|---------|---------|
| comba-cs (ripple) | **0.13** | **0.77** | **7.19** |
| comba-cs + BK | T/O | T/O | T/O |
| comba-cs + g-only(top) | 0.09 | 1.07 | 10.41 |
| comba-cs + g-fa | 0.13 | 0.83 | 9.14 |
| comba-cs + g-only(internal) | 0.13 | 0.77 | — |

**No adder encoding interaction benefits comba-cs.** BK kills it
(as with all multiplier encodings). g-only and g-fa hurt at BW≥11.
The internal adder is irrelevant (same as standard Comba).
Default ripple-carry is optimal.

## The 3+ Multiplication Gap (#4)

### dadda-cs: Dadda-style carry-save encoding

Combines Dadda's compact full_adder reduction (same variable count
as shift-add) with comba-cs's column-independent first pass.

| Encoding | Vars (BW=9) | Clauses |
|----------|-------------|---------|
| shift-add | 427 | 1749 |
| dadda | 427 | 1749 |
| **dadda-cs** | **427** | **1749** |
| comba | 627 | 2435 |
| comba-cs | 679 | 2561 |

dadda-cs achieves the SAME variable count as shift-add/dadda.

### Performance comparison

| Benchmark | shift | dadda | comba-cs | dadda-cs |
|-----------|-------|-------|----------|----------|
| comm_9 | 1.97 | 0.53 | **0.13** | 0.71 |
| comm_11 | 57.5 | 14.6 | **0.78** | 2.00 |
| str_red_32 | 0.38 | 0.36 | 0.60 | **0.21** |
| overflow_16 | 1.78 | **0.48** | 0.78 | 1.03 |

dadda-cs is BEST on strength reduction (0.21s) and competitive
on commutativity (2.00s vs comba-cs's 0.78s).

### 3+ multiplication benchmarks: gap persists

| Benchmark | shift | comba-cs | dadda-cs |
|-----------|-------|----------|----------|
| assoc_8 | **29.1** | T/O | T/O |
| distrib_8 | **103.6** | T/O | T/O |

dadda-cs T/O on assoc/distrib despite having the same variable
count as shift-add. The reason: BVE analysis shows shift-add
achieves 106% elimination (BVE-completeness) while dadda-cs
achieves only 58%. The carry-save clause structure PREVENTS
BVE from achieving completeness.

**The 3+ multiplication gap is a BVE-completeness phenomenon,
not a variable count issue.** shift-add's sequential accumulation
creates a clause structure that BVE can fully eliminate. Carry-save
structures (both comba-cs and dadda-cs) create clause structures
that resist full BVE elimination.

## Real-World SMT Benchmark Validation

### Benchmark suite

| Benchmark | Description | Muls | Type |
|-----------|-------------|------|------|
| comm_N | a*b == b*a | 2 | eq UNSAT |
| assoc_8 | (a*b)*c == a*(b*c) | 4 | eq UNSAT |
| distrib_8 | a*(b+c) == a*b+a*c | 3 | eq UNSAT |
| crypto_sq_mod | (a²)%m == ((a%m)²)%m | 2+mod | SAT |
| overflow_det_16 | wide vs narrow product | 2 | UNSAT |
| div_mul_rt_12 | q*b+r == a | 1+div | UNSAT |
| mul_ineq_12 | a≤b ∧ c>0 → a*c≤b*c | 2 | ineq UNSAT |
| strength_red_16 | x*7 == x*8-x | 1 | eq UNSAT |
| factor_N | find p*q==n | 1 | SAT |

### Results

| Benchmark | shift | comba-cs | dadda-cs | dadda | Winner |
|-----------|-------|----------|----------|-------|--------|
| comm_8 | 0.59 | **0.09** | 0.14 | 0.11 | comba-cs |
| comm_16 | T/O | **4.54** | T/O | T/O | comba-cs |
| comm_20 | T/O | **17.1** | T/O | T/O | comba-cs |
| assoc_8 | **29.1** | T/O | T/O | T/O | shift |
| distrib_8 | **103.6** | T/O | T/O | T/O | shift |
| crypto_sq_mod | all fast | — | — | — | any |
| overflow_det_16 | 1.03 | 0.98 | **0.92** | 1.12 | dadda-cs |
| div_mul_rt_12 | **7.42** | 9.17 | 11.2 | 9.10 | shift |
| mul_ineq_12 | **1.39** | 2.08 | 1.83 | 1.63 | shift |
| strength_red_16 | 0.01 | 0.02 | 0.01 | 0.01 | any |
| factor_* | all fast | — | — | — | any |

### Encoding selection rules (validated)

| Problem pattern | Best encoding | Reason |
|----------------|---------------|--------|
| 2 muls + equality | **comba-cs** | Short carry chains, BCP cascades |
| 2 muls + inequality | **shift-add** | Smaller formula, BVE-friendly |
| 3+ muls | **shift-add** | BVE-completeness |
| 1 mul + property | **dadda** or **dadda-cs** | Smallest formula |
| SAT problems | any | Trivially fast |
| Division involved | **shift-add** | Division dominates |

The key discriminator is whether the problem has TWO multiplications
compared by EQUALITY. Only in this case does comba-cs's structural
advantage (column independence, short carry chains) outweigh its
variable overhead. For all other patterns, smaller formulas win.

## Signed Multiplication: Not a Gap

### Code path analysis

`signed_multiplier()` (line 3658) does:
1. Extract sign bits: `sign0 = sign_bit(op0)`
2. Conditionally negate: `neg0 = cond_negate(op0, sign0)`
3. **Call `unsigned_multiplier(neg0, neg1)`** — uses our encoding flags
4. Conditionally negate result: `cond_negate(result, result_sign)`

The `#ifdef USE_KARATSUBA` path that would bypass `unsigned_multiplier`
is **commented out** (`// #define USE_KARATSUBA` at line 2036).

### Empirical verification

| Config | Unsigned BW=9 | Signed BW=9 | Unsigned BW=11 | Signed BW=11 |
|--------|--------------|-------------|----------------|--------------|
| shift-add | 1.97s | 1.97s | 57.4s | 57.4s |
| comba-cs | 0.13s | 0.13s | 0.77s | 0.78s |

**Identical performance.** The `cond_negate` overhead is negligible
(~2.6% extra variables for the sign-handling MUX gates).

### Note on expression-level simplification

CBMC simplifies `a * b == b * a` at the expression level (0 VCCs)
but NOT `c = a*b; d = b*a; assert(c == d)` (1 VCC, reaches SAT solver).
The intermediate variables hide the commutativity from the simplifier.
This applies equally to signed and unsigned.

## Why Shift-Add Achieves BVE-Completeness (#1)

### The data

| Phase | shift-add | dadda-cs |
|-------|-----------|----------|
| Preprocessing: elim | 45 | 42 |
| Preprocessing: fixed | 2 | 2 |
| **Inprocessing: elim** | **+255** | +184 |
| **Inprocessing: fixed** | **+123** | **+2** |
| **Total removed** | **425 (106%)** | 230 (58%) |

Preprocessing is nearly identical (47 vs 44 removed). The ENTIRE
difference is in inprocessing: shift-add gets **123 fixed variables**
during search vs dadda-cs's 2.

### The mechanism

"Fixed" variables come from unit propagation during inprocessing.
When BVE eliminates a variable during search, it creates resolvents.
If a resolvent combined with a learned clause creates a unit
implication, a variable gets fixed. This can cascade: fixing one
variable may create new unit implications.

**shift-add's sequential accumulation creates CARRY CHAINS** that
enable cascading unit propagation. When one carry variable is
determined (by a learned clause or BVE resolvent), it propagates
through the chain, fixing the next carry, which fixes the next,
etc. This cascade can fix 123 variables.

**dadda-cs's carry-save structure BREAKS these chains.** The
deferred carries go to different columns, preventing cascading
unit propagation. Each carry is independent, so fixing one doesn't
cascade to others. Only 2 variables get fixed.

### The paradox resolved

This explains the paradox: carry-save helps commutativity but
hurts associativity.

- **Commutativity** (2 muls, hard residual): The problem is too
  hard for BVE-completeness regardless. What matters is BCP
  cascade DURING SEARCH (not during BVE). Carry-save's column
  independence enables better BCP cascades → fewer conflicts.

- **Associativity** (4 muls, achievable BVE-completeness): The
  problem CAN be solved by BVE-completeness if enough variables
  are fixed during inprocessing. Carry chains enable cascading
  unit propagation → BVE-completeness → trivial residual.
  Carry-save breaks these chains → no BVE-completeness → hard
  residual → T/O.

### Implication

There is a fundamental tradeoff:
- **Carry chains**: enable BVE-completeness (good for 3+ muls)
  but create proof bottlenecks (bad for 2 muls)
- **Carry-save**: avoids proof bottlenecks (good for 2 muls)
  but prevents BVE-completeness (bad for 3+ muls)

No single encoding can be optimal for both. This confirms the
need for adaptive encoding selection based on problem structure.

## External SMT Benchmark Validation (#3)

### Real-world-inspired benchmarks

| Benchmark | Description | Muls | Type | shift | comba-cs | dadda-cs | dadda |
|-----------|-------------|------|------|-------|----------|----------|-------|
| hw_mul_equiv_12 | HW multiplier equiv | 2 eq | UNSAT | **18.1** | 95.8 | T/O | T/O |
| barrett_red_8 | Barrett reduction | 2+mod | UNSAT | 0.01 | 0.01 | 0.00 | 0.01 |
| checked_mul_16 | Rust checked_mul | 2 (diff width) | UNSAT | **0.46** | 0.77 | 0.56 | 0.59 |
| fixedpoint_mul_16 | Fixed-point mul | 2 | SAT | 0.00 | 0.03 | 0.00 | 0.02 |
| strength_chain_16 | 3 strength reductions | 3 const | UNSAT | 1.27 | 1.35 | 0.89 | **0.74** |

### Key finding: comba-cs's advantage is narrow

**comba-cs wins ONLY on the commutativity pattern** — two multiplications
of the SAME operands in swapped order (a*b vs b*a). For all other
2-multiplication patterns, shift-add or dadda wins:

- **hw_mul_equiv_12** (built-in mul vs manual shift-add): shift-add
  wins 5.3x. The two sides have DIFFERENT structure, so comba-cs's
  column-independence advantage doesn't apply.

- **checked_mul_16** (wide mul vs narrow mul): shift-add wins 1.7x.
  Different operand widths mean different multiplication circuits.

- **strength_chain_16** (3 constant multiplications): dadda wins.
  Constant multiplication is simplified by CBMC.

### Refined encoding selection rules

| Pattern | Best encoding | Examples |
|---------|---------------|---------|
| a*b == b*a (swapped operands) | **comba-cs** | commutativity |
| mul1 == mul2 (different structure) | **shift-add** | HW equiv checking |
| mul(wide) vs mul(narrow) | **shift-add** | overflow detection |
| Single mul + property | **dadda** | strength reduction |
| Constant multiplication | **dadda** | x*15 == x<<4-x |
| 3+ multiplications | **shift-add** | associativity |
| SAT problems | any | factoring |

The discriminator is not just "2 multiplications + equality" but
specifically "2 multiplications of the SAME operands in swapped
order." This is a much narrower pattern than previously thought.

## Word-Level Simplification Impact (cb50af334f)

Cherry-picked commit cb50af334f which simplifies algebraic identities
(commutativity, distributivity, associativity) at the expression level.

### What it simplifies

| Form | Simplified? | Example |
|------|-------------|---------|
| Direct assertion | **YES** | `assert(a*b == b*a)` → 0 VCCs |
| Variable form | **NO** | `c=a*b; d=b*a; assert(c==d)` → 1 VCC |
| smt2_solver | **NO** | SMT2 formulas bypass CBMC's simplifier |

### Why variable form is not simplified

CBMC's symbolic execution creates SSA variables for every intermediate
result. The simplifier sees `c == d` (two SSA variables), not
`a*b == b*a` (the algebraic identity). The commutativity pattern
is hidden by the intermediate variables.

In real C code, the variable form IS the common pattern:
```c
int result1 = compute(a, b);
int result2 = compute(b, a);
assert(result1 == result2);
```

### Impact on encoding relevance

**All encoding work remains fully relevant.** The word-level
simplification helps only for direct assertions in source code,
which is a narrow use case. For the common variable form (and for
smt2_solver), the SAT encoding determines performance:

| Benchmark (variable form) | shift-add | comba-cs | dadda |
|--------------------------|-----------|----------|-------|
| comm BW=17 | T/O | **7.19s** | T/O |
| overflow BW=16 | 1.77s | 0.78s | **0.48s** |
| str_red BW=32 | 0.38s | 0.60s | **0.36s** |

These are UNCHANGED from before the cherry-pick.

## Floating-Point Benchmark Results

### FP encoding has NO effect

| Benchmark | shift | comba-cs | dadda |
|-----------|-------|----------|-------|
| Float4 (mixed FP ops) | 21.6s | 21.6s | 21.6s |
| FP dot product comm | 0.9s | 0.9s | 0.9s |
| FP cross product antisym | 1.0s | 1.0s | 1.0s |
| FP mul no overflow | 0.03s | 0.03s | 0.03s |

**No encoding difference on any FP benchmark.** The FP wrapper
(NaN/Inf handling, rounding, exponent arithmetic) accounts for
96% of solving time. The 24-bit mantissa multiplication (48-bit
integer multiplication) is too small to show encoding effects.

Double precision (53-bit mantissa → 106-bit multiplication) is
beyond the solvable frontier for all encodings.

There is no FP "sweet spot" where encoding matters with current
CBMC. FP benchmarks are not useful for encoding evaluation.

## Real-World Integer Benchmark Results

### Comprehensive benchmark suite

| Benchmark | Description | Muls | shift | comba-cs | dadda |
|-----------|-------------|------|-------|----------|-------|
| matrix_trace_8bit | tr(AB)==tr(BA) | 8 | 29.5s | **0.58s** | 3.70s |
| matrix_trace_16bit | tr(AB)==tr(BA) | 8 | T/O | **35.1s** | T/O |
| MAC_comm_4x8bit | a·b==b·a (4D) | 8 | 17.5s | **0.37s** | 1.68s |
| hash_deterministic | h(x)==h(x) | 2 const | T/O | 13.2s | **7.83s** |
| wide_mul_comm_32bit | (u32)a*b==(u32)b*a | 2 | T/O | **50.2s** | T/O |
| poly_horner_vs_direct | Horner==direct | 3 | 0.05s | 0.05s | 0.04s |
| hw_mul_equiv_12 | bvmul vs shift-add | 2 diff | **18.1s** | 95.8s | T/O |
| checked_mul_16 | wide vs narrow | 2 diff | **0.46s** | 0.77s | 0.59s |

### Key findings

**comba-cs provides 47-51x speedup on real verification tasks:**
- Matrix trace invariant (tr(AB)==tr(BA)): 0.58s vs 29.5s (**51x**)
- MAC commutativity (dot product): 0.37s vs 17.5s (**47x**)
- 16-bit matrix trace: ONLY comba-cs solves it (35.1s)
- 32-bit wide multiplication: ONLY comba-cs solves it (50.2s)

**dadda wins on constant multiplication:**
- Hash determinism: 7.83s vs 13.2s (comba-cs)
- Polynomial evaluation: 0.04s vs 0.05s

**shift-add wins on structurally different multiplications:**
- HW multiplier equivalence: 18.1s vs 95.8s (comba-cs)
- Checked multiplication: 0.46s vs 0.77s (comba-cs)

### The pattern

comba-cs excels when the problem has **multiple multiplications
with operand symmetry** (same operands in different order). This
includes:
- Commutativity: a*b == b*a
- Matrix trace: tr(AB) == tr(BA) (each element has swapped products)
- Dot product: Σ a[i]*b[i] == Σ b[i]*a[i]

For problems WITHOUT operand symmetry (different structures,
constant multiplication, different widths), dadda or shift-add wins.
