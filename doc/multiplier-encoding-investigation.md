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
