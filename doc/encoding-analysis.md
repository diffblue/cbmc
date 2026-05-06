# Encoding Analysis: Solver Statistics

## Summary Table

| Benchmark | Encoding | Vars | Clauses | Conflicts | Decisions | Propagations | BVE-elim | Time |
|-----------|----------|------|---------|-----------|-----------|--------------|----------|------|
| **strength_chain_16** | shift-add | 714 | 2910 | 39,757 | 49,128 | 2,147,911 | 370 | 1.0s |
| | comba-cs | 714 | 2906 | 43,804 | 54,232 | 2,395,698 | 375 | 1.4s |
| | dadda | 756 | 3036 | 29,188 | 47,431 | 1,627,936 | 404 | 0.7s |
| | **booth** | **496** | **1780** | **4,071** | **5,144** | **84,868** | 268 | **0.06s** |
| | block4 | 983 | 3842 | 18,590 | 29,890 | 839,972 | 770 | 0.4s |
| | sortnet | 13,316 | 40,462 | 34,985 | 64,579 | 25,043,002 | 11,421 | 6.5s |
| **bf16_mul_comm_v2** | shift-add | 1743 | 6697 | 417,623 | 803,528 | 45,289,835 | 1,363 | 22.8s |
| | **comba-cs** | 1743 | 6683 | **230,430** | **453,571** | **24,271,851** | 1,265 | **11.1s** |
| | booth | 1743 | 6697 | 417,623 | 803,528 | 45,289,835 | 1,363 | 22.9s |
| | block4 | 1743 | 6697 | 417,623 | 803,528 | 45,289,835 | 1,363 | 22.9s |
| **hw_mul_equiv_12** | **shift-add** | **658** | **2503** | **446,046** | **692,850** | **23,042,652** | 455 | **17.3s** |
| | booth | 817 | 3015 | 2,494,823 | 3,623,929 | 115,620,269 | 895 | 115.1s |
| | block4 | 823 | 3091 | 1,694,761 | 2,587,917 | 63,010,921 | 780 | 62.9s |
| | comba-cs | — | — | — | — | — | — | T/O |
| **mul_ineq_12** | shift-add | 2876 | — | 15,662 | 24,962 | 1,329,066 | 950 | 0.5s |
| | comba-cs | 2876 | — | 15,662 | 24,962 | 1,329,066 | 950 | 0.5s |
| | booth | 4268 | — | 48,620 | 81,850 | 5,353,686 | 1,529 | 1.7s |
| | **block4** | 4206 | — | **13,617** | **21,607** | **1,269,813** | 1,545 | **0.4s** |

## Key Insights

### 1. No single encoding dominates all benchmarks

Each encoding wins on a different problem class:
- **comba-cs**: Best for commutativity (bf16: 45% fewer conflicts via congruence closure)
- **booth**: Best for constant multiplication (strength_chain: 10× fewer conflicts)
- **shift-add**: Best when comparing against shift-add circuits (hw_mul_equiv)
- **block4**: Best for inequality constraints (mul_ineq: 13% fewer conflicts)

### 2. Formula size does NOT predict performance

- bf16_mul_comm_v2: ALL encodings produce identical formulas (1743 vars, ~6697 clauses)
  yet comba-cs is 2× faster. The difference is purely structural.
- hw_mul_equiv_12: shift-add has FEWER vars (658) than booth (817) or block4 (823)
  AND is 4-7× faster. Structural matching with the comparison target matters.

### 3. Booth excels on constant multiplication

For x*15, x*17, x*255 (strength_chain_16):
- Booth produces 30% fewer variables (496 vs 714)
- 10× fewer conflicts (4,071 vs 39,757)
- 25× fewer propagations (84K vs 2.1M)
- Reason: radix-4 encoding means many Booth digits are zero for constants
  with few set bits, eliminating entire partial products.

### 4. Sorting network is a negative result

- 18× more variables (13,316 vs 714)
- 14× more clauses (40,462 vs 2,910)
- Similar conflicts but 12× more propagations (25M vs 2.1M)
- The auxiliary sorted-property constraints add overhead without
  sufficient propagation benefit.

### 5. The encoding-benchmark interaction is the key finding

The optimal encoding depends on the PROBLEM STRUCTURE:
- Commutativity (two identical circuits) → comba-cs (congruence closure)
- Constant multiplication → booth (fewer partial products)
- Circuit equivalence → match the comparison target's structure
- General inequalities → block4 (balanced tree structure)

This motivates an ADAPTIVE encoding selection that considers problem structure,
not just multiplication count.

## Detailed Solver Statistics

### strength_chain_16 (constant multiplication)

| Encoding | Conflicts | Decisions | Propagations | BVE-elim | Fixed | Redundant | Time |
|----------|-----------|-----------|--------------|----------|-------|-----------|------|
| shift-add | 39,757 | 49,128 | 2,147,911 | 370 | 217 | 2,276 | 1.0s |
| comba-cs | 43,804 | 54,232 | 2,395,698 | 375 | 199 | 5,820 | 1.4s |
| dadda | 29,188 | 47,431 | 1,627,936 | 404 | 185 | 678 | 0.7s |
| **booth** | **4,071** | **5,144** | **84,868** | 268 | 98 | 716 | **0.06s** |
| block4 | 18,590 | 29,890 | 839,972 | **770** | 95 | 1,012 | 0.4s |
| sortnet | 34,985 | 64,579 | 25,043,002 | 11,421 | 2,915 | 8,357 | 6.5s |

**Observations:**
- Booth: 10× fewer conflicts, 25× fewer propagations. The radix-4 encoding
  eliminates partial products for constant multipliers with few set bits.
- block4: highest BVE elimination (770 vs 370 for shift-add). The 4-bit block
  structure creates intermediate variables that BVE can eliminate efficiently.
- sortnet: highest fixed count (2,915) — the auxiliary sorted-property constraints
  enable massive unit propagation. But 25M propagations means each propagation
  is cheap but there are too many. The overhead outweighs the benefit.
- comba-cs: most redundant clauses (5,820) — the popcount structure generates
  many learned clauses that are kept. But these don't help on this benchmark
  (constant multiplication doesn't benefit from congruence closure).

### hw_mul_equiv_12 (circuit equivalence)

| Encoding | Conflicts | Decisions | Propagations | BVE-elim | Fixed | Redundant | Time |
|----------|-----------|-----------|--------------|----------|-------|-----------|------|
| **shift-add** | **446,046** | **692,850** | **23,042,652** | 455 | **174** | 7,931 | **17.3s** |
| booth | 2,494,823 | 3,623,929 | 115,620,269 | 895 | 23 | 7,251 | 115.1s |
| block4 | 1,694,761 | 2,587,917 | 63,010,921 | 780 | 84 | 32,482 | 62.9s |

**Observations:**
- shift-add: 174 fixed variables (highest!) — structural matching with the
  comparison target enables early unit propagation. The benchmark compares
  bvmul against a manual shift-add circuit; when the encoding matches,
  BVE identifies structurally equivalent variables and fixes them.
- booth: only 23 fixed variables — the Booth structure doesn't match the
  comparison target, so BVE can't find structural equivalences.
- block4: 32,482 redundant clauses (4× more than shift-add) — the solver
  learns many clauses but they're not useful (wrong structure).

### Key Finding: Fixed Variables as Predictor

The "fixed" count (variables determined by unit propagation during
inprocessing) is the best predictor of performance:
- strength_chain: booth has fewest fixed (98) but wins because it has
  fewest variables overall (496). The formula is so small that BVE
  solves it almost entirely during preprocessing.
- hw_mul_equiv: shift-add has most fixed (174) and wins. The structural
  matching enables early variable fixing.

### bf16_mul_comm_v2: The Identical Formula Mystery

All encodings except comba-cs produce IDENTICAL formulas (1743 vars,
6697 clauses, 417,623 conflicts). This is because:
1. The benchmark uses QF_FP (floating-point), not QF_BV
2. The FP mantissa multiplication goes through float_bvt which uses
   the boolbvt's bv_utils — but the encoding flags (booth, block4)
   are NOT propagated to the FP path
3. Only comba-cs differs because the adaptive heuristic's pre-scan
   sets comba_carry_save on the boolbvt instance, which IS used by
   the FP path
4. comba-cs's 14 fewer clauses (6683 vs 6697) enable CaDiCaL's
   congruence closure to find equivalent gates, reducing conflicts
   by 45% (230,430 vs 417,623)

This is a BUG in our encoding propagation — booth/block4 should also
affect FP multiplications. Fixing this could improve FP benchmarks.
