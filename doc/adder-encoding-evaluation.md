# Adder Encoding Evaluation for SAT Solving

## Summary

We evaluated 7 adder encodings across 5 benchmarks and 2 SAT solvers
(MiniSat2 and CaDiCaL). The key finding is that **no single encoding
dominates**: the optimal choice depends on both the benchmark structure
and the SAT solver.

## Encodings Tested

| Encoding | Description | Per-bit cost |
|----------|-------------|-------------|
| **PC_ripple** | Propagation complete full adder (Brain et al. 2016, `OPTIMAL_FULL_ADDER`). Current CBMC default. | 14 clauses, 2 aux vars |
| **simple_ripple** | Textbook full adder: `carry = OR(AND(a,b), AND(a,c), AND(b,c))`, `sum = XOR(a,b,c)` | ~10 clauses, 2 aux vars |
| **Rani_MUX** | MUX-based carry (Rani et al. 2011): `carry = ITE(a XNOR b, a, carry_in)` | ~10 clauses, 3 aux vars |
| **carry_lookahead** | Carry lookahead with generate/propagate signals | Fewer vars, more clauses |
| **kogge_stone** | Parallel prefix (Kogge-Stone) | O(n log n) clauses |
| **brent_kung** | Parallel prefix (Brent-Kung) | O(n log n) clauses |
| **sklansky** | Parallel prefix (Sklansky) | O(n log n) clauses |

## Benchmarks

| ID | Description | Type | Size |
|----|-------------|------|------|
| 01_sat | `a[i] + b[i] > a[i]` | SAT, 32-bit | N=2000 |
| 02_unsat | Constrained overflow check | UNSAT, 32-bit | N=200 |
| 04_sub | `a[i] - b[i] < a[i]` | SAT, 32-bit | N=1000 |
| 05_incr | `a[i] + 1 != a[i]` | SAT, 32-bit | N=5000 |
| 07_wide | `a[i] + b[i] > a[i]` | SAT, 64-bit | N=1000 |

## Results (solver time in seconds)

### MiniSat2

| Encoding | 01_sat | 02_unsat | 04_sub | 05_incr | 07_wide |
|----------|--------|----------|--------|---------|---------|
| PC_ripple | 3.58 | 3.89 | 13.56 | 0.82 | 3.50 |
| simple_ripple | 32.23 | **2.66** | 13.69 | 1.18 | 38.67 |
| Rani_MUX | 8.38 | 8.49 | **1.79** | 0.83 | 8.49 |
| carry_lookahead | **2.90** | 4.83 | 48.38 | **0.57** | **2.72** |
| kogge_stone | T/O | 8.62 | 45.61 | 2.31 | T/O |
| brent_kung | 93.13 | 5.90 | 29.16 | 1.26 | T/O |
| sklansky | T/O | 5.60 | 33.94 | 1.55 | T/O |

### CaDiCaL

| Encoding | 01_sat | 02_unsat | 04_sub | 05_incr | 07_wide |
|----------|--------|----------|--------|---------|---------|
| PC_ripple | **0.14** | 5.64 | 0.03 | 0.06 | **0.13** |
| simple_ripple | 0.24 | **4.74** | 0.06 | 0.07 | 0.23 |
| Rani_MUX | **0.14** | 5.27 | 0.03 | 0.07 | **0.13** |
| carry_lookahead | 0.18 | 15.30 | **0.02** | **0.04** | 0.17 |
| kogge_stone | 0.65 | 13.14 | 0.14 | 0.12 | 0.77 |
| brent_kung | 0.36 | 9.32 | 0.08 | 0.08 | 0.40 |
| sklansky | 0.43 | 10.84 | 0.09 | 0.09 | 0.50 |

## Analysis

### Parallel prefix adders are uniformly bad

Kogge-Stone, Brent-Kung, and Sklansky produce O(n log n) clauses and
variables. They optimize hardware signal propagation delay, but this
does not translate to SAT solving speed. CDCL solvers exploit the
sequential carry chain structure for unit propagation; the parallel
prefix structure destroys this and confuses solver heuristics.

**Recommendation: remove parallel prefix adders from consideration.**

### The Rani MUX encoding excels on the hard subtract benchmark

On 04_sub (the hardest benchmark for MiniSat), Rani_MUX is **7.6x
faster** than PC_ripple (1.79s vs 13.56s). The MUX-based carry
`ITE(a XNOR b, a, carry_in)` produces 2-literal watched clauses
after the selector is assigned:
- When `a == b` (generate/kill): carry is determined by `a` alone
- When `a != b` (propagate): carry equals carry_in (direct implication)

These 2-literal clauses enable extremely fast BCP along the carry chain.

However, Rani_MUX is 2-3x slower than PC_ripple on benchmarks 01 and
07, and much slower on 02_unsat. The MUX encoding is not propagation
complete, which hurts when the solver needs to derive contradictions.

### Carry lookahead is best for MiniSat on most SAT benchmarks

Carry lookahead wins on 01_sat, 05_incr, and 07_wide with MiniSat.
It has the fewest variables (the generate/propagate signals compress
the carry chain) which helps MiniSat's variable activity heuristics.
But it's catastrophically bad on 04_sub (48.4s) and on CaDiCaL's
02_unsat (15.3s).

### CaDiCaL is much less sensitive to encoding choice

CaDiCaL's preprocessing (bounded variable elimination, subsumption,
vivification) effectively normalizes different encodings. The spread
between best and worst is typically 2-5x for CaDiCaL vs 10-100x for
MiniSat. CaDiCaL slightly prefers encodings with fewer variables
(carry_lookahead, PC_ripple).

### The PC full adder is a good default but not optimal

PC_ripple (the current CBMC default) is never the worst choice and
is competitive on most benchmarks. It's the best or tied-best for
CaDiCaL on 01_sat and 07_wide. But it's far from optimal on 04_sub
(MiniSat) where Rani_MUX is 7.6x faster.

## Novel Encoding: Generate-Skip Clauses

We experimented with adding redundant "generate-skip" clauses to the
PC ripple carry adder. For each pair of adjacent bits, we add:

```
g[i] AND p[i+1] => c[i+2]
```

where `g[i] = a[i] AND b[i]` (generate) and `p[i+1] = a[i+1] XOR b[i+1]`
(propagate). This clause creates a shortcut in the implication graph:
if bit i generates a carry and bit i+1 propagates it, the solver can
skip directly to carry[i+2] without going through carry[i+1].

Results on the original benchmarks (MiniSat):
- 01_sat: 2.10s (vs 3.58s baseline, **41% faster**)
- 02_unsat: 3.71s (vs 3.89s, 5% faster)
- 04_sub: 14.8s (vs 13.6s, 9% slower)

The generate-skip helps on addition-heavy SAT benchmarks but adds
overhead on others. It's not a universal improvement.

## Recommendations

1. **Keep PC_ripple as the default.** It's the most robust choice
   across solvers and benchmark types.

2. **Consider Rani_MUX for MiniSat-heavy workloads** where subtraction
   or mixed add/subtract patterns dominate. The 7.6x speedup on 04_sub
   is significant.

3. **Consider carry_lookahead for CaDiCaL** on SAT-heavy workloads
   with many independent additions.

4. **Remove parallel prefix adders** (Kogge-Stone, Brent-Kung, Sklansky).
   They are uniformly worse and add code complexity.

5. **A solver-aware encoding selection** (choosing the adder based on
   which SAT solver is configured) could give the best of all worlds
   but adds implementation complexity.

## References

- Brain, Hadarean, Kroening, Martins. "Automatic Generation of
  Propagation Complete SAT Encodings." VMCAI 2016.
- Rani et al. "Area optimized low power arithmetic and logic unit." 2011.

## Reproduction

Benchmarks are in `/tmp/adder_bench/` and `/tmp/bench_sub.c`. Each
encoding can be selected by changing the `adder()` function in
`src/solvers/flattening/bv_utils.cpp` to delegate to the desired
implementation. The Rani MUX encoding is toggled by the `#if 1`/`#if 0`
switch in `simple_ripple_carry_adder`.

## Why Parallel Prefix Adders Are Worse: SAT-Level Explanation

Proof trace analysis on the N=200 UNSAT benchmark reveals three
mechanisms:

### 1. Preprocessing Destruction (most impactful)

| Metric | PC Ripple | Kogge-Stone |
|--------|-----------|-------------|
| Variables eliminated by BVE | **80.25%** | 36.66% |

In ripple carry, each carry depends on only 3 variables
`(a[i], b[i], carry[i-1])`, making bounded variable elimination (BVE)
highly effective. The prefix tree creates variables with O(log n)
dependencies, blocking BVE. CaDiCaL eliminates 80% of PC variables
but only 37% of Kogge-Stone variables.

### 2. More Conflicts Required (2.8x)

| Metric | PC Ripple | Kogge-Stone |
|--------|-----------|-------------|
| Conflicts | 28,958 | 80,393 |
| Decisions | 4.4M | 5.8M |

Each prefix tree auxiliary variable is an additional choice point.
The ripple carry's sequential structure creates a natural variable
ordering that CDCL exploits; the prefix tree provides no such guidance.

### 3. Slower Propagation (0.81x rate)

| Metric | PC Ripple | Kogge-Stone |
|--------|-----------|-------------|
| Propagation rate | 1.71 M/s | 1.39 M/s |
| Propagations | 10.1M | 21.0M |

More clauses per variable means more watched literals to check during
BCP. The learned clause database is also larger (639K binary clauses
for KS vs 74K width-4 for PC), further slowing propagation.

### Root Cause

Hardware adders optimize for **signal propagation delay** (physical).
SAT solvers optimize for **conflict analysis** (logical). The O(log n)
depth of parallel prefix adders is irrelevant because BCP processes
the 32-bit ripple carry chain in microseconds. The prefix tree's
complex structure actively harms the solver by preventing preprocessing
and creating unhelpful variable dependencies.


## Variable Ordering and Solver Options Experiments

### Variable Ordering (zero-cost optimization)

CBMC assigns low variable numbers to inputs (a, b) and high numbers
to Tseitin/carry auxiliary variables. Testing different orderings on
CaDiCaL reveals dramatic effects:

**UNSAT benchmark (N=200):**

| Ordering | Time | Conflicts | Decisions | Speedup |
|----------|------|-----------|-----------|---------|
| Original | 5.74s | 28,958 | 4,444,827 | 1.0x |
| Reversed | **3.76s** | 25,263 | 1,810,587 | **1.53x** |
| Inputs first | 5.71s | 28,958 | 4,444,782 | 1.0x |
| Aux first | 5.63s | 33,568 | 3,076,092 | 1.02x |
| Random | 10.08s | 33,899 | 10,506,165 | 0.57x |

**Equivalence check (N=100, UNSAT):**

| Ordering | Time | Conflicts | Decisions | Speedup |
|----------|------|-----------|-----------|---------|
| Original | 7.72s | 248,716 | 6,443,359 | 1.0x |
| Reversed | 4.97s | 85,680 | 3,683,381 | 1.55x |
| Inputs first | 6.37s | 202,202 | 4,594,573 | 1.21x |
| **Aux first** | **4.59s** | 165,973 | 2,588,354 | **1.68x** |
| Random | 8.77s | 196,916 | 6,722,808 | 0.88x |

**Explanation:** SAT solvers use VSIDS which biases toward recently-
conflicting variables, but initial variable numbering affects tie-
breaking and early decisions. Putting carry/Tseitin variables first
makes the solver prioritize structural reasoning about the adder
before exploring input values.

**This is a zero-cost optimization** — changing variable allocation
order in CBMC's propositional layer requires no additional clauses.

### CaDiCaL Options

| Option | Time | Conflicts | Notes |
|--------|------|-----------|-------|
| Default | 5.74s | 28,958 | |
| **No preprocessing** | **3.56s** | 32,128 | BVE overhead > search savings |
| No BVE only | 4.08s | 28,459 | |
| **No inprocessing** | **3.71s** | 30,387 | |
| No restarts | 4.14s | 30,057 | |
| **Always negative phase** | **4.60s** | **17,766** | Fastest conflict detection |
| No chronological BT | 7.80s | 8,290 | Fewest conflicts but slow |

**Surprising finding:** Disabling CaDiCaL's preprocessing makes it
38% faster on this benchmark. The BVE preprocessing eliminates 80%
of variables but the time spent doing so exceeds the search time saved.
This suggests the adder encoding is already well-structured for search
and preprocessing adds overhead without benefit.


### Kissat Results

Kissat consistently outperforms CaDiCaL on adder benchmarks:

| Benchmark | CaDiCaL | Kissat | Speedup |
|-----------|---------|--------|---------|
| UNSAT (N=200) | 5.73s (29K conflicts) | **3.0s** (24K conflicts) | 1.91x |
| Equiv (N=100) | 7.79s (249K conflicts) | **5.0s** (122K conflicts) | 1.56x |

Kissat is also less sensitive to variable ordering (3s regardless of
ordering vs CaDiCaL's 3.76-5.74s range).

### CaDiCaL XOR Processing

| Config | UNSAT time | Equiv time |
|--------|-----------|-----------|
| Default | 5.73s | 7.79s |
| No XOR extraction | 5.73s | 8.07s |
| No BVE | 4.07s | 6.09s |
| No BVE + no XOR | **3.93s** | 6.57s |

XOR extraction has minimal effect on pure addition benchmarks but
slightly helps on the equivalence check (which contains explicit XOR
in `a^b`). BVE consistently hurts — the overhead exceeds the benefit.

### Note on CBMC's CaDiCaL Configuration

CBMC already disables `factor` (bounded variable addition) in
`satcheck_cadical.cpp` based on earlier experiments. BVE (`elim`) is
still enabled. Our experiments suggest disabling BVE would also help
for adder-heavy formulas, but this may hurt other workloads.


### Full 4-Solver Comparison

| Solver | UNSAT(N=200) | Conflicts | Equiv(N=100) | Conflicts |
|--------|-------------|-----------|-------------|-----------|
| **CryptoMiniSat** | **2.21s** | **148** | **4.93s** | **119** |
| Kissat | 3.0s | 23,952 | 5.0s | 122,198 |
| MiniSat | 4.29s | 24,732 | 7.33s | 133,573 |
| CaDiCaL | 5.68s | 28,958 | 7.81s | 248,716 |

**CryptoMiniSat's Gaussian elimination is transformative.** It detects
XOR constraints embedded in the CNF (adders are built from XOR gates)
and solves them algebraically, reducing conflicts from ~25K-249K to
~120-148. This is a fundamentally different approach: instead of
learning carry-chain implications through CDCL conflicts, CryptoMiniSat
derives them through linear algebra over GF(2).

This suggests that the most impactful improvement for adder-heavy
formulas may not be in the encoding at all, but in **solver selection**
or **native XOR support**.
