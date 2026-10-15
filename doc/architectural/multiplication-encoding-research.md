# Multiplication Encoding Research Notes

## Objective

Find a propositional encoding of multiplication that SAT solvers can reason
about as efficiently as possible. This is an open research problem — even
state-of-the-art SMT solvers (Bitwuzla, Z3, CVC5) struggle with
multiplication at moderate bitwidths.

## Benchmark Suite

### Commutativity: `a * b == b * a`
Tests whether the solver can prove the algebraic identity. Uses
`__CPROVER_bitvector[N]` for exact bitwidth control.

```c
// multiply-comm.c
int main() {
  __CPROVER_bitvector[BITWIDTH] a, b;
  __CPROVER_bitvector[BITWIDTH] c = a * b;
  __CPROVER_bitvector[BITWIDTH] d = b * a;
  __CPROVER_assert(c == d, "commutativity");
}
```

### Associativity: `(a * b) * c == a * (b * c)`
Much harder — involves three multiplications.

```c
// multiply-assoc.c
int main() {
  __CPROVER_bitvector[BITWIDTH] a, b, c;
  __CPROVER_bitvector[BITWIDTH] ab = a * b;
  __CPROVER_bitvector[BITWIDTH] bc = b * c;
  __CPROVER_assert(ab * c == a * bc, "associativity");
}
```

### Distributivity: `a * (b + c) == a * b + a * c`

```c
// multiply-distrib.c
int main() {
  __CPROVER_bitvector[BITWIDTH] a, b, c;
  __CPROVER_assert(a * (b + c) == a * b + a * c, "distributivity");
}
```

### Factoring: given `n`, find `p * q == n`
Tests the reverse direction — SAT solver must find factors.

```c
// multiply-factor.c
int main() {
  __CPROVER_bitvector[BITWIDTH] p, q;
  __CPROVER_assume(p > 1 && q > 1);
  __CPROVER_assert(p * q != COMPOSITE, "not factorable");
}
```

### Multiply-by-constant: `a * K == a + a + ... + a`

```c
// multiply-const.c
int main() {
  __CPROVER_bitvector[BITWIDTH] a;
  __CPROVER_assert(a * 3 == a + a + a, "multiply by 3");
}
```

### Square identity: `(a + b)^2 == a^2 + 2*a*b + b^2`

```c
// multiply-square.c
int main() {
  __CPROVER_bitvector[BITWIDTH] a, b;
  __CPROVER_bitvector[BITWIDTH] sum = a + b;
  __CPROVER_assert(sum * sum == a*a + 2*a*b + b*b, "square identity");
}
```

## Encoding Schemes Tested

### 1. Baseline (shift-add with ripple-carry)
The default CBMC encoding. Each bit of one operand selects (AND) the other
operand, shifted by the bit position. Partial products are summed using
ripple-carry addition.

- Formula size: O(n²) variables and clauses
- Carry chain depth: O(n²) — long dependency chains
- Uses propagation-complete full adder (14 clauses)

### 2. Dadda Tree
Reduces partial products using Dadda's sequence of full/half adders to
minimize the number of adders used. Produces two rows (carry-save form),
then does a final ripple-carry addition.

- Same formula size as baseline (same number of full adders, different wiring)
- Different clause ordering affects solver heuristics
- Better than baseline with CaDiCaL on large bitwidths (see code comments)

### 3. Wallace Tree
Similar to Dadda but reduces columns as aggressively as possible at each
stage. Slightly larger than Dadda.

- Generally worse than Dadda in benchmarks

### 4. Comba (popcount-based column reduction)
**Current best performer.** Reduces each column independently using the
parallel bit-counting algorithm (Hacker's Delight popcount). Each column's
sum is a binary number; high bits carry to the next column.

- Formula size: ~2x larger than Dadda/baseline
- BUT: ~30x faster with CaDiCaL at BW=11
- The extra auxiliary variables from popcount create balanced trees that
  enable better unit propagation
- Key insight: formula size is anti-correlated with performance here

### 5. Radix-8 (higher radix partial products)
Pre-computes x*0 through x*7 to reduce the number of partial products by
3x. Can be combined with any reduction scheme.

- Helps at larger bitwidths when combined with Dadda
- Overhead of pre-computation hurts at small bitwidths

### 6. Karatsuba
Divide-and-conquer: splits n-bit multiplication into three (n/2)-bit
multiplications. Asymptotically O(n^1.585) vs O(n²).

- Implemented in the PR but not benchmarked yet

### 7. Toom-Cook
Generalization of Karatsuba using polynomial interpolation. Splits into
more pieces for better asymptotic complexity.

- Implemented in the PR, based on the Brain paper's approach
- Allows incremental tightening of over-approximation

### 8. Schönhage-Strassen
Based on the number-theoretic transform. O(n log n log log n) complexity.

- Implemented in the PR but has a bug: `bvt b = a;` in the last commit
  makes it compute a*a instead of a*b
- Needs fixing and benchmarking

## Benchmark Results

All results use `__CPROVER_bitvector[N]` with `--no-standard-checks`.
Timeout: 300s. Commutativity uses intermediate variables.

### Commutativity: `c=a*b; d=b*a; assert(c==d)`

| Variant | BW=9 | BW=11 | BW=13 | BW=15 | BW=17 | BW=19 |
|---------|------|-------|-------|-------|-------|-------|
| baseline+CaDiCaL | 2.01s | 60.8s | >300s | >300s | >300s | >300s |
| **comba+CaDiCaL** | **0.26s** | **1.75s** | **8.08s** | **10.4s** | **46.4s** | **177s** |
| dadda+CaDiCaL | 0.54s | 14.1s | 180s | >300s | >300s | >300s |
| baseline+MiniSat | 5.35s | 251s | >300s | >300s | >300s | >300s |
| comba+MiniSat | 6.12s | 272s | >300s | >300s | >300s | >300s |
| dadda+MiniSat | 12.1s | >300s | >300s | >300s | >300s | >300s |
| **Bitwuzla** | **0.03s** | **0.03s** | **0.02s** | **0.02s** | **0.03s** | **0.03s** |
| **Z3** | 0.04s | 0.04s | 0.04s | 0.04s | 0.04s | 0.04s |

### Primality: prove n has no factors (wide multiplication)

| Variant | BW=20 | BW=24 | BW=28 | BW=30 | BW=32 | BW=34 |
|---------|-------|-------|-------|-------|-------|-------|
| **baseline+CaDiCaL** | **0.11s** | **0.42s** | **1.46s** | **3.33s** | **6.38s** | **13.8s** |
| comba+CaDiCaL | 0.16s | 0.72s | 3.09s | 5.49s | 9.76s | 17.3s |
| dadda+CaDiCaL | 0.11s | 0.63s | 2.12s | 5.02s | 9.71s | 17.0s |
| baseline+MiniSat | 0.07s | 0.26s | 1.63s | 3.66s | 7.70s | 33.2s |
| comba+MiniSat | 0.10s | 0.40s | 2.01s | 5.26s | 40.2s | 83.2s |
| dadda+MiniSat | 0.07s | 0.27s | 1.35s | 4.81s | 9.25s | 28.5s |
| **Bitwuzla** | 0.22s | 0.68s | **1.51s** | **2.94s** | 7.36s | **13.9s** |
| Z3 | 0.21s | 0.59s | 3.56s | 6.68s | 15.9s | 39.6s |

### AWS real-world proofs

| Encoding | aws_mul_checked | aws_list_back | aws_mul_sat |
|----------|-----------------|---------------|-------------|
| baseline+CaDiCaL | 2.53s | 6.10s | 1.24s |
| comba+CaDiCaL | 39.4s | 8.45s | 8.84s |
| **dadda+CaDiCaL** | **1.29s** | **5.75s** | **1.20s** |
| **wallace+CaDiCaL** | **1.19s** | 6.45s | 1.27s |
| radix8+CaDiCaL | 6.97s | 4.62s | 5.06s |
| karatsuba+CaDiCaL | 3.89s | >120s | 3.25s |
| toom-cook+CaDiCaL | >120s | >120s | >120s |
| schönhage+CaDiCaL | >120s | >120s | >120s |
| **Bitwuzla** | **0.83s** | **1.63s** | **1.52s** |
| Z3 | 1.05s | 1.65s | 7.93s |
| CVC5 | 1.10s | 4.93s | 2.79s |

### All encodings on all benchmark types (CaDiCaL)

| Encoding | comm 9 | comm 13 | prime 20 | prime 28 | aws_mul | aws_back | aws_sat |
|----------|--------|---------|----------|----------|---------|----------|---------|
| baseline | 2.01s | >300s | 0.11s | 1.46s | 2.53s | 6.10s | 1.24s |
| **comba** | **0.26s** | **8.08s** | 0.16s | 3.09s | 39.4s | 8.45s | 8.84s |
| dadda | 0.54s | 180s | 0.11s | 2.12s | **1.29s** | 5.75s | 1.20s |
| wallace | 1.89s | >300s | 0.14s | 1.87s | **1.19s** | 6.45s | 1.27s |
| radix8 | 1.37s | >300s | 0.14s | 1.87s | 6.97s | **4.62s** | 5.06s |
| radix8+dadda | 1.36s | >300s | 0.14s | 1.87s | 7.03s | **4.62s** | 5.10s |
| karatsuba | 5.54s | 10.0s | 0.88s | 69.7s | 3.89s | >120s | 3.25s |
| toom-cook | 2.48s | 31.4s | 9.24s | 71.7s | >120s | >120s | >120s |
| schönhage | 86.4s | >300s | >120s | >120s | >120s | >120s | >120s |

### Refinement modes (comba+CaDiCaL, --refine-arithmetic)

| Mode | comm 9 | comm 13 | prime 20 | prime 28 | aws_mul | aws_back |
|------|--------|---------|----------|----------|---------|----------|
| 0 (original) | 0.64s | 17.9s | 0.28s | 7.30s | 13.1s | 21.2s |
| 1 (assumption) | 0.67s | 15.7s | 0.32s | 7.36s | 13.1s | 14.5s |
| 2 (karatsuba) | 0.84s | 13.2s | 1.16s | 53.1s | 14.3s | 25.8s |
| 3 (toom-cook) | 0.74s | 25.9s | 0.50s | 6.93s | 15.2s | 12.3s |

### Summary

1. **No single encoding wins everywhere.** Comba dominates commutativity
   (8x faster than baseline at BW=13), Dadda/Wallace dominate AWS proofs
   (30x faster than Comba on aws_mul_checked), Baseline is best for
   primality.

2. **CaDiCaL consistently outperforms MiniSat** on commutativity (10-50x).
   On primality, MiniSat is competitive at small BW but falls behind at
   BW≥32.

3. **Bitwuzla dominates** on commutativity (instant at any BW) and AWS
   proofs (0.83s vs best CBMC 1.19s). On primality it's competitive with
   baseline CaDiCaL.

4. **Refinement modes don't help** on primality or AWS proofs. Mode 2
   (Karatsuba) helps slightly on commutativity but hurts on primality.

5. **Schönhage-Strassen and Toom-Cook are too expensive** at BW≤40.

6. **Growth rates**: commutativity (comba+CaDiCaL) ~4x per 2 bits;
   primality (baseline+CaDiCaL) ~2x per 2 bits.

## Key Insights

### 1. Formula size is NOT the right optimization target
Comba produces 2x more clauses than Dadda but is 30x faster. The extra
auxiliary variables from popcount create a structure that enables better
unit propagation. This aligns with the Brain et al. "Automatic Generation
of Propagation Complete SAT Encodings" paper.

### 2. Auxiliary variables that "summarize" groups of bits help propagation
The popcount algorithm creates intermediate variables that represent the
count of 1-bits in groups of 2, 4, 8, etc. These act as abstractions that
the SAT solver can reason about at a higher level.

### 3. Balanced tree depth matters
Replacing popcount with a simple full-adder tree (same clause count as
Dadda) gives 25x worse performance than popcount. The balanced tree
structure of popcount (O(log n) depth) vs the sequential chain of
full-adders (O(n) depth) is critical.

### 4. CaDiCaL consistently outperforms MiniSat on multiplication
Likely due to better preprocessing (bounded variable elimination,
subsumption) and inprocessing techniques.

### 5. CaDiCaL has XOR gate extraction
CaDiCaL's congruence closure module extracts XOR gates from CNF
(`congruencexor` option, enabled by default, arity limit 4). The full-adder
sum is a 3-input XOR, which is within the arity limit. This likely explains
why CaDiCaL outperforms MiniSat on multiplication — it recognizes the XOR
structure that MiniSat treats as opaque clauses.

**Verified experimentally**: For BW=9 commutativity, CaDiCaL extracts:
- 131 XOR gates
- 138 AND gates
- 130 congruent pairs (corresponding gates in the two multiplier circuits)

For BW=5 distributivity (which is much harder):
- 205 XOR gates extracted
- 0 congruent pairs (the three multiplier circuits have different structures)
- 44K conflicts (vs 11K for commutativity BW=9)

The congruence closure is key for commutativity — it discovers that
corresponding gates in the two multiplier circuits are equivalent. For
distributivity, this doesn't help because the circuits have different
operands.

Increasing the XOR arity limit from 4 to 16 had no effect — the default
is already sufficient for the 3-input XOR in full adders.

### 6. SMT solvers use word-level reasoning, not bit-blasting
Z3 sees `(bvmul a b)` and `(bvmul b a)` at the word level and can
immediately recognize commutativity as a trivial rewrite. It never
bit-blasts algebraic identities. This means **the right approach for
algebraic properties is word-level reasoning, not better bit-blasting**.
However, for problems that genuinely require bit-level reasoning (factoring,
hardware verification), bit-blasting is necessary.

### 7. Redundant clauses don't help much
Tested adding:
- LSB constraint: `result[0] == op0[0] AND op1[0]`
- Zero-operand constraint: if operand is 0, result is 0
- MSB constraint: if top halves of operands are 0, top half of result is 0

Results were mixed — slight improvements at some bitwidths, regressions at
others. The overhead of the extra clauses offsets any propagation benefit.

### 8. Schönhage-Strassen is too expensive for small bitwidths
The SS encoding produces 43K variables and 227K clauses for BW=7 (vs ~600
for Comba). It's designed for very large numbers (thousands of bits) where
O(n log n log log n) beats O(n²). For our target range (7-32 bits), it's
orders of magnitude worse.

### 9. Intermediate variables matter for benchmark design
`assert(a*b == b*a)` is 13x slower than `c=a*b; d=b*a; assert(c==d)`.
The inline version creates a combined circuit; the intermediate variable
version creates separate circuits that the solver can reason about
independently.

### 10. `--refine-arithmetic` exists but needs stronger initial approximation
CBMC's `--refine-arithmetic` implements abstraction-refinement for
multiplication. It starts with `x*0=0` and `x*1=x` as initial constraints
and refines incrementally. For BW=9 commutativity, it takes 11 iterations
and 0.65s (vs 0.26s for direct Comba). For BW=11, it's 6.08s vs 1.78s.
The initial approximation is too weak — adding algebraic properties
(commutativity, distributivity) as initial constraints could make many
benchmarks trivial.

### 11. Word-level commutativity simplification is highly effective
Adding a check in `simplify_inequality` that recognizes `a op b == b op a`
for commutative operators (mult, plus, bitand, bitor, bitxor) and simplifies
to `true` makes commutativity verification instant at ANY bitwidth (tested
up to 256-bit). The simplification fires during expression simplification,
before any bit-blasting occurs. This is exactly the word-level reasoning
that Z3 does.

**Limitation**: Only works for inline expressions (`assert(a*b == b*a)`),
not through intermediate variables (`c=a*b; d=b*a; assert(c==d)`). The
latter would require value propagation or common subexpression elimination
to expose the pattern to the simplifier.

### 12. Word-level distributivity simplification also works
Added recognition of `a * (b + c) == a * b + a * c` (and commuted
variants) in `simplify_inequality`. Expands multiplication over addition
on each side and compares with deep commutativity checking. Makes
distributivity verification instant at any bitwidth (tested up to 128-bit).

### 13. CryptoMiniSat's native XOR doesn't help
CryptoMiniSat5 (with native XOR clause support) is 2-25x slower than
CaDiCaL on all multiplication benchmarks. CaDiCaL's congruence closure
(which discovers equivalent gates between multiplier circuits) is more
effective than CryptoMiniSat's XOR handling.

| BW | CaDiCaL | CryptoMiniSat5 |
|----|---------|----------------|
| 7 | 0.10s | 0.36s |
| 9 | 0.26s | 6.69s |
| 11 | 1.78s | >60s |

### 14. Optimal encoding is solver-dependent
For MiniSat2, the **Baseline (shift-add)** encoding is actually faster
than Comba (5.19s vs 6.00s at BW=9, 249s vs 273s at BW=11). MiniSat
lacks CaDiCaL's congruence closure and XOR extraction, so Comba's extra
auxiliary variables are just noise. This means the encoding choice should
ideally depend on the solver being used.

| BW | MiniSat+Baseline | MiniSat+Comba | CaDiCaL+Comba |
|----|-----------------|--------------|--------------|
| 7 | 0.42s | 0.41s | 0.10s |
| 9 | 5.19s | 6.00s | 0.26s |
| 11 | 249s | 273s | 1.78s |

### 15. Associativity simplification via leaf-set comparison
Flattening nested applications of associative+commutative operators and
comparing the sorted multisets of leaves handles associativity:
`(a*b)*c == a*(b*c)` both flatten to `{a, b, c}`. Instant at any bitwidth.

### 16. Assumption-gated incremental refinement works
Implemented two-stage refinement in `--refine-arithmetic` using
solve-with-assumptions:

**Stage 0**: Build a narrow multiplier (low 4 bits of operands,
zero-extended to full width) gated by a retractable assumption literal.

**Stage 1+**: Drop the gate assumption and add the full multiplier.
Key fix: if `check_SAT` finds concrete values match at stage 0 but the
overall property still fails (re-entry), force the full multiplier.

| BW | Original | Assumption-gated | Speedup |
|----|----------|-----------------|---------|
| 7 | 0.14s | 0.03s | 4.7x |
| 9 | 0.65s | 0.04s | 16x |
| 11 | 6.10s | 0.04s | 152x |

### 17. Toom-Cook with non-deterministic coefficients implemented
Implemented the Brain paper's polynomial interpolation approach:
- Split operands into 4-bit chunks
- Create free coefficient variables d[i] for the result polynomial
- Constrain: result = sum(d[i] * 2^(i*chunk))
- Add evaluation points incrementally (r(0), r(1), then full fallback)

Correct on all benchmarks but slower than assumption-gated at small
bitwidths (0.21s vs 0.03s for comm BW=7). Would benefit at larger
bitwidths where sub-multiplications are much cheaper than full.

## AMulet2 / Algebraic Approach (from Kaufmann & Biere 2023)

The AMulet2 tool verifies multiplier circuits using Gröbner bases over Z[X].
Key ideas:
- Each gate is modeled as a polynomial (e.g., AND: -u + vw = 0)
- The specification is checked to reduce to zero modulo the gate polynomials
- Complex final-stage adders (Kogge-Stone, etc.) are replaced with
  ripple-carry adders (verified equivalent via SAT), then the simplified
  circuit is verified algebraically
- XOR-based slicing reduces the problem size

This is fundamentally different from bit-blasting — it reasons about the
algebraic structure of the circuit. The approach is specific to verifying
known circuit implementations, not general multiplication.

## Open Questions

1. **The polynomial view unification**: Toom-Cook/Karatsuba decompose
   multiplication as polynomial evaluation/interpolation BEFORE encoding
   to propositional logic. AMulet2 reasons about gate polynomials
   (`AND: -u + vw = 0`) AFTER the circuit exists. These are the same
   mathematical framework applied at different levels. The key unexploited
   insight: if we could recognize polynomial identities (commutativity,
   distributivity) at the expression level and simplify them before
   creating any circuit, we'd avoid the exponential blowup entirely.
   This is what Z3 does for simple cases.

2. **Strengthening `--refine-arithmetic`**: CBMC already has
   abstraction-refinement for multiplication (starts with `x*0=0` and
   `x*1=x`, refines incrementally via `--refine-arithmetic`). However,
   it's currently slower than direct Comba encoding (6.08s vs 1.78s at
   BW=11 commutativity, 11 refinement iterations). The initial
   approximation is too weak — it doesn't include algebraic properties
   like commutativity. If the refinement started with stronger word-level
   properties, it could potentially solve algebraic identities without
   ever fully encoding the multiplier.

3. Can we systematically identify which "summary" auxiliary variables
   help propagation? The popcount's effectiveness suggests balanced-tree
   summaries are key. This connects to the propagation completeness
   theory from Brain et al. 2016.

4. For distributivity, the solver needs to discover that multiplication
   distributes over addition — a property requiring reasoning about the
   interaction between multiplier and adder circuits. Can we add
   word-level "bridge" constraints that connect these?

5. Is there a way to encode the multiplier that makes algebraic structure
   more visible to the SAT solver? E.g., encoding partial products so
   that commutativity/distributivity are apparent at the clause level.

## Recommended Next Steps (Priority Order)

1. **Add MiniSat to the full benchmark matrix** — quick gap-fill.

2. **Strengthen `--refine-arithmetic` with algebraic properties** — the
   existing infrastructure supports abstraction-refinement. Adding
   commutativity (`a*b == b*a`), distributivity (`a*(b+c) == a*b + a*c`),
   and other word-level properties as initial constraints could make many
   benchmarks trivial without full bit-blasting. This is the highest-impact
   direction and builds on existing CBMC infrastructure.

3. **Try CryptoMiniSat** on the benchmarks — it has native XOR support
   which could help since the full-adder sum is XOR.

4. **Explore the Toom-Cook incremental approach** — connects to the
   incremental symex work and could provide a systematic way to refine
   multiplication approximations.

5. **Investigate word-level preprocessing in CBMC's expression simplifier**
   — extend it to recognize and simplify algebraic identities involving
   multiplication before bit-blasting.

## Literature

### Brain 2021, "Further Steps Down The Wrong Path"
- Multiplication by constant: use contiguous-1s trick (128-1 instead of
  127) and pattern sharing
- Toom-Cook polynomial interpolation: allows incremental approximation
- Key result: propagation-complete multiplier is likely exponential in size
- Suggests algebraic techniques (Gröbner bases) are more promising

### Brain et al. 2016, "Automatic Generation of Propagation Complete SAT Encodings"
- Formalizes propagation completeness using abstract satisfaction
- Algorithm to generate PCEs automatically
- Key finding: carry bits are the critical auxiliary variables for addition
- PC full-adder: 14 clauses (used by CBMC)
- PC 2x2 multiplier: 19 clauses
- Composition of PC primitives is PC for adders but NOT for multipliers

## TODO

- [ ] Implement proper Toom-Cook incremental refinement using
      over-approximation constraints (polynomial evaluation points with
      non-deterministic coefficients, not bit-slicing)
- [ ] Study whether Comba advantage holds on real-world CBMC benchmarks
- [ ] Make encoding choice solver-dependent (Comba for CaDiCaL, Baseline
      for MiniSat)
- [ ] Profile CaDiCaL to understand where time is spent
- [ ] Investigate square identity simplification (requires polynomial
      normalization)

## Real-World Benchmark Sources

1. **aws-c-common proofs** (used by CBMC's perf-benchcomp CI): Array
   operations involve multiplication for index computation
   (`count * element_size`). The `aws_mul_size_checked` proof directly
   verifies a multiplication function.

2. **Floating-point verification**: FP multiplication involves integer
   multiplication of mantissas. CBMC's FP support uses this extensively.

3. **SMT-LIB QF_BV benchmarks** (fmv.jku.at/smtbench/): Standard
   benchmark suite for bit-vector solvers, includes multiplication-heavy
   problems from hardware verification.

4. **Cryptographic code**: Hash functions (SHA, MD5) and ciphers (AES)
   use multiplication in GF(2^n). These are a natural source of hard
   multiplication problems.

Note: Most real-world CBMC usage involves multiplication by constants
(array indexing, struct field offsets) which is already handled efficiently
by constant propagation. Symbolic × symbolic multiplication is rarer but
occurs in checked arithmetic, cryptography, and FP verification.

## Bitwuzla Deep Study

### How Bitwuzla solves multiplication problems instantly

Bitwuzla uses a multi-stage pipeline that avoids bit-blasting for most
algebraic identities:

1. **Rewriter** (`NORMALIZE_COMM`): Sorts operands of commutative operators
   by node ID. After this, `a*b` and `b*a` are the same expression.
   Then `EQUAL_TRUE` recognizes `x == x` → `true`.

2. **Rewriter** (`NORM_FACT_BV_ADD_MUL`): Factorizes `a*b + a*c` into
   `a*(b+c)` by finding common factors. This handles distributivity.

3. **Preprocessing** (`normalize_comm_assoc`): Flattens nested
   additions/multiplications, computes occurrence maps, factors out
   common subterms, and normalizes both sides of equalities to a
   canonical form. This handles associativity and complex identities.

4. **Bit-blasting**: Only invoked if the above steps don't resolve the
   formula. Uses AIG-based bit-blasting (more compact than direct CNF)
   with CaDiCaL as the SAT backend.

### Key commit: c0184571 (March 21, 2025)

Author: Mathias Preiner. Added 8 normalization rewrite rules:
- `NORM_FACT_BV_ADD_MUL`: factorize `a*b + a*c → a*(b+c)`
- `NORM_FACT_BV_ADD_SHL`: factorize additions involving shifts
- `NORM_FACT_BV_SHL_MUL` / `NORM_FACT_BV_MUL_SHL`: shift/multiply
- `NORM_BV_EXTRACT_ADD_MUL_REV*`: extract over add/mul
- `NORM_BV_MUL_POW2_REV`: multiply by power of 2

This single commit (434 lines) is what makes Bitwuzla solve all our
algebraic identity benchmarks instantly.

### Normalization preprocessing pass (January 2023 onwards)

The `PassNormalize` preprocessing pass (`normalize.cpp`) implements:
- Flattening of nested BV_ADD and BV_MUL
- Occurrence counting for common subterm factoring
- Canonical ordering of terms
- Score-based AIG complexity estimation

This is essentially the polynomial normalization we identified as the
"right approach" — Bitwuzla implements it as a preprocessing pass.

### What CBMC could learn from Bitwuzla

1. **Operand normalization** (sort commutative operands by ID) — we
   implemented this in `simplify_inequality` but Bitwuzla does it at
   the expression construction level, making it universal.

2. **Factorization rewrite** (`a*b + a*c → a*(b+c)`) — we implemented
   this in `simplify_inequality` but Bitwuzla applies it as a general
   rewrite rule, not just in equality contexts.

3. **Polynomial normalization** (flatten + occurrence counting + common
   subterm factoring) — this is the key missing piece in CBMC. It would
   handle associativity, the square identity, and other complex
   algebraic properties that our current simplifier cannot.

4. **AIG-based bit-blasting** — Bitwuzla uses And-Inverter Graphs as
   an intermediate representation before CNF conversion. This allows
   structural hashing and simplification that direct CNF generation
   misses.
