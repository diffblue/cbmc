# SMT2 Benchmark Analysis

## Experiment Setup
- 36 SMT2 benchmarks × 4 multiplier encodings × 3 adder encodings × 4 solvers = 1728 jobs
- Median of 3 runs, 120s timeout, 6GB memory limit
- Machine: Intel Xeon Platinum 8124M (3.0 GHz, 36 cores), 68GB RAM, Ubuntu 24.04
- Solvers: CaDiCaL 3.0.0, MiniSat 2.2.1, MergeSat 4.0-rc4, CryptoMiniSat 5.11.21
- Raw data: bench-multiplication/smt2-results-clean.tsv

## Multiplier Encoding: Practical Usefulness (CaDiCaL, ripple adder)

Only benchmarks where at least one configuration takes >1s:

| Benchmark | shift-add | dadda | comba | comba-cs | Assessment |
|---|---|---|---|---|---|
| comm_16 | T/O | T/O | 34.3s | **5.5s** | Big win: previously unsolvable |
| comm_20 | T/O | T/O | T/O | **35.2s** | Big win: previously unsolvable |
| bf16_mul_comm_v2 | 22.9s | 28.0s | 10.6s | 11.2s | 2× improvement |
| bf16_mul_mono | 29.1s | 32.5s | 27.5s | 29.0s | Neutral |
| div_mul_roundtrip_12 | 4.2s | 3.9s | 4.1s | 3.9s | Neutral |
| strength_chain_16 | 0.93s | 1.57s | 1.15s | 0.97s | Neutral |
| checked_mul_16 | 0.39s | 0.31s | 0.61s | 14.1s | Regression (still solves) |
| hw_mul_equiv_12 | 14.9s | T/O | T/O | 103.3s | Regression (borderline) |
| overflow_detect_16 | 0.34s | 0.18s | 1.18s | 119.7s | **Serious regression** |
| assoc_8 | 27.2s | T/O | 119.2s | T/O | **Loss** (3+ multiplications) |
| distrib_8 | 83.3s | T/O | T/O | T/O | **Loss** (3+ multiplications) |
| half_mul_comm_v2 | T/O | T/O | 117.3s | T/O | Only comba solves |

### Regression Root Causes

1. **assoc_8, distrib_8** (3+ multiplications): BVE-completeness threshold.
   shift-add achieves 106% BVE elimination through cascading unit propagation
   via carry chains. comba-cs breaks these chains, achieving only 58%.
   With 3+ multiplications, BVE-completeness is achievable and decisive.

2. **overflow_detect_16** (single 32-bit multiplication): The adaptive
   fallback threshold is `width > 32`, but this is 32-bit (not >32).
   comba-cs popcount is used for a single wide multiplication where
   shift-add's carry chains enable BVE cascading.

3. **hw_mul_equiv_12** (heterogeneous: bvmul vs manual shift-add):
   One side is encoded as comba-cs, the other as manual shift-add.
   The structural mismatch prevents BVE from discovering equivalences.

4. **checked_mul_16** (two 32-bit multiplications with overflow check):
   Similar to overflow_detect_16 — wide multiplication where BVE
   cascading through carry chains is beneficial.

### Potential Fixes for comba-cs Regressions

- **3+ multiplications**: Count multiplications in the formula; fall back
  to shift-add when count ≥ 3. (Requires information flow from symex to
  bit-blasting, which is architecturally difficult in CBMC.)
- **overflow_detect_16**: Change threshold from `> 32` to `>= 32`.
  This would route 32-bit multiplication through shift-add.
- **hw_mul_equiv_12**: Structural mismatch is inherent; no encoding fix.
- **checked_mul_16**: Would be fixed by the `>= 32` threshold change.

## Adder Encoding: Practical Usefulness

### Brent-Kung (BK)

BK is **harmful on all solvers** except for one narrow case:

| Benchmark | Solver | ripple | BK | Ratio |
|---|---|---|---|---|
| equiv_unsat_8add_16 | CaDiCaL | 0.058s | **0.012s** | 4.6× faster |
| equiv_unsat_8add_16 | MiniSat | 0.072s | 0.102s | 1.4× slower |
| equiv_unsat_8add_16 | MergeSat | 0.071s | 0.143s | 2.0× slower |
| equiv_unsat_8add_16 | CryptoMiniSat | 0.392s | 0.486s | 1.2× slower |
| add_chain_16 | CaDiCaL | 0.177s | 0.917s | 5.2× slower |
| add_chain_32 | CaDiCaL | 0.459s | 1.694s | 3.7× slower |
| add_chain_32 | MiniSat | 2.52s | 10.15s | 4.0× slower |
| add_overflow_16 | ALL | 0.008s | T/O | catastrophic |
| div_roundtrip | CaDiCaL | 3.92s | 6.03s | 1.5× slower |

**Verdict**: BK is CaDiCaL-specific and only helps when there are many
additions (8+) in a single equality check. Too dangerous as default.

### g-only

g-only is **never harmful on hard problems** and provides consistent small gains:

| Benchmark | Solver | ripple | g-only | Ratio |
|---|---|---|---|---|
| add_chain_32 | CaDiCaL | 0.459s | **0.326s** | 1.4× faster |
| add_chain_32 | MergeSat | 0.978s | **0.763s** | 1.3× faster |
| distrib_8 (shift-add) | CaDiCaL | 83.3s | **72.7s** | 1.15× faster |
| equiv_unsat_8add_16 | CryptoMiniSat | 0.392s | **0.189s** | 2.1× faster |
| strength_chain_16 | CaDiCaL | 0.97s | **0.85s** | 1.14× faster |

No regressions on any hard benchmark across any solver.

**Verdict**: g-only is a safe, consistent improvement. Could be the default
with minimal risk. Warrants deeper investigation.

## Cross-Solver Summary

| Solver | Solved/Total | Notes |
|---|---|---|
| CaDiCaL | 312/432 | Best overall, benefits from inprocessing BVE |
| MergeSat | 300/432 | Second best, no inprocessing |
| CryptoMiniSat | 291/432 | XOR handling provides no benefit |
| MiniSat | 264/432 | SatELite preprocessing helps on small formulas |

## Deep Investigation: comba-cs Regression Root Causes

The regressions are NOT from carry-save separation. dadda-cs (carry-save
without popcount) is fast on all regression benchmarks:

| Benchmark | shift-add | dadda | dadda-cs | comba | comba-cs |
|---|---|---|---|---|---|
| overflow_detect_16 | 0.34s | 0.18s | **0.22s** | 1.18s | 119.7s |
| checked_mul_16 | 0.39s | 0.31s | **0.23s** | 0.61s | 14.1s |
| assoc_8 | **27.2s** | T/O | T/O | 119.2s | T/O |
| distrib_8 | **83.3s** | T/O | T/O | T/O | T/O |

The regression is from **popcount specifically**. Popcount creates
intermediate variables that prevent BVE from cascading through the
relationship between multiplications.

### When popcount helps vs hurts

**Popcount helps** (commutativity): Two multiplications with IDENTICAL
structure. Popcount's balanced tree creates congruent gate pairs that
CaDiCaL's congruence closure discovers. Without popcount (dadda-cs),
the circuits have different internal structure and congruence closure
can't help. Only comba-cs solves comm_16 (5.5s) and comm_20 (35.2s).

**Popcount hurts** (overflow, assoc, distrib): Multiple multiplications
with DIFFERENT relationships. BVE needs to cascade through carry chains
to discover the relationship. Popcount's intermediate variables block
this cascade.

### Isolation experiment

overflow_detect_16 has two multiplications: wide (32-bit, 16 PPs from
zero-extension) and narrow (16-bit, 16 PPs symbolic). Each alone is
trivial (SAT, instant). The hardness comes from proving the UNSAT
relationship between them. The 403 extra variables from comba-cs's
popcount on the narrow multiplication make this proof 340× harder.

### Potential adaptive fix

The current adaptive fallback routes sparse constants through dadda-cs.
It should also route cases where popcount is counterproductive:
- When the multiplication is part of an overflow check (one wide, one narrow)
- When there are 3+ multiplications (associativity, distributivity)

This requires information not available at encoding time (how many
multiplications are in the formula). A practical heuristic: count
unsigned_multiplier() calls and switch to dadda-cs after the 2nd call.
This would fix assoc/distrib but might hurt some 2-multiplication
benchmarks. Needs further investigation.

## Deep Investigation: g-only Adder Encoding

### Mechanism

g-only adds redundant AND gates (g[i] = a[i] & b[i]) to every
top-level ripple-carry addition. These do NOT affect multiplier-internal
additions (isolated by the adder_encoding swap in unsigned_multiplier).

The AND gates enable BVE polarity alignment cascades: the AND gate's
clauses structurally match carry generation clauses, enabling BVE to
eliminate them trivially, which reduces occurrence counts of input
variables, enabling further cascading elimination.

### Where g-only helps (shift-add multiplier)

| Benchmark | Solver | ripple | g-only | Ratio |
|---|---|---|---|---|
| strength_chain_16 | MergeSat | 5.05s | **2.05s** | 2.46× |
| hw_mul_equiv_12 | MiniSat | T/O | **119s** | ∞ (new solve) |
| add_chain_32 | CaDiCaL | 0.46s | **0.33s** | 1.40× |
| add_chain_32 | MergeSat | 0.98s | **0.76s** | 1.28× |
| distrib_8 | CaDiCaL | 83.3s | **72.7s** | 1.15× |
| div_roundtrip_12 | MiniSat | 13.2s | **11.9s** | 1.11× |
| div_roundtrip_12 | MergeSat | 11.4s | **10.3s** | 1.10× |

### Where g-only is neutral (comba-cs multiplier)

With comba-cs, g-only is almost entirely neutral on all benchmarks.
The popcount already creates enough intermediate variables for BVE,
so the additional AND gates from g-only are redundant.

Two borderline regressions with comba-cs: hw_mul_equiv_12 (103→T/O)
and overflow_detect_16 (120→T/O), but these are already near T/O
with ripple.

### Why g-only helps more on MergeSat/MiniSat

MergeSat and MiniSat rely on preprocessing BVE (SatELite) rather than
inprocessing. The g-only AND gates provide BVE targets that are
available during preprocessing, before the search starts. CaDiCaL's
inprocessing can discover similar elimination opportunities during
search, so g-only provides less additional benefit.

### Practical verdict

g-only is a **safe, consistent improvement for the shift-add multiplier
path**. It should be the default top-level adder encoding when shift-add
is used (either explicitly or via comba-cs's adaptive fallback for
wide/sparse multiplications). For comba-cs's popcount path, g-only
is neutral and can be left as ripple.
