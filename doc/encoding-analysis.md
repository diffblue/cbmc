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
