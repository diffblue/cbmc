# Algebraic Methods for Bit-Vector Verification

## Status: Level 2 implemented, smt2 integration ready

## Level 1: Word-Level Simplification (IMPLEMENTED)

Commit cb50af334f (already in features/adder branch as 7c766b8c26).

Handles:
- Commutativity: `a*b == b*a` → true (operand swap)
- Associativity: `(a*b)*c == a*(b*c)` → true (leaf-set flattening)
- Distributivity: `a*(b+c) == a*b + a*c` → true (one-level expansion)
- FOIL: `(a+b)*(c+d) == a*c + a*d + b*c + b*d` → true
- 4-way associativity: `a*(b*(c*d)) == ((a*b)*c)*d` → true

Does NOT handle:
- Square identity: `(a+b)^2 == a^2 + 2*a*b + b^2` (needs polynomial normalization)
- Intermediate variables: `c = a*b; d = b*a; assert(c == d)` (SSA hides structure)

Limitation: only works when algebraic structure is visible in a single
expression. Intermediate variables (from SSA, user code, or compiler)
hide the structure. This is why comba-cs is still needed for the
intermediate-variable case.

## smt2_solver Algebraic Integration (Ready to Implement)

### Root Cause of Current Limitation

In cbmc, SSA encoding creates intermediate variables:
```
c#1 = a#0 * b#0    →  set_to(equal(c#1, mult(a#0, b#0)), true)
d#1 = b#0 * a#0    →  set_to(equal(d#1, mult(b#0, a#0)), true)
assert(c#1 == d#1)  →  set_to(equal(c#1, d#1), false)
```
The algebraic solver sees 3 equations: `c - a*b = 0`, `d - b*a = 0`,
`(c-d)*e - 1 = 0`. Gröbner basis proves UNSAT in 0.0002s.

In smt2_solver, expressions are inline (no SSA):
```
(assert (not (= (bvmul a b) (bvmul b a))))
→  set_to(not(equal(mult(a,b), mult(b,a))), true)
```
The algebraic solver sees 0 equalities and 1 disequality. The
disequality becomes `(a*b - b*a)*e - 1 = 0` — a single equation
that the Gröbner basis cannot prove UNSAT from alone.

### Fix: Decompose Inline Expressions in poly_extractort

When `to_polynomial()` encounters a multiplication with non-trivial
operands, introduce a fresh variable and add the defining equation
to a side-channel list:

```cpp
// In poly_extractort:
std::vector<polynomialt> side_equations;

// In to_polynomial(), when encountering ID_mult:
if(e.id() == ID_mult && /* operands are non-trivial */) {
  // Recursively convert operands
  auto op0_poly = to_polynomial(e.operands()[0]);
  auto op1_poly = to_polynomial(e.operands()[1]);
  // Introduce fresh variable
  std::size_t fresh = get_var_index("__fresh_" + std::to_string(next_fresh++));
  polynomialt fresh_var{bw, 1, fresh};
  // Add defining equation: fresh - op0 * op1 = 0
  side_equations.push_back(fresh_var - (*op0_poly * *op1_poly));
  // Return the fresh variable (not the product)
  return fresh_var;
}
```

This way, `extract_equation(equal(mult(a,b), mult(b,a)))` produces:
1. Side equation: `c - a*b = 0` (from converting mult(a,b))
2. Side equation: `d - b*a = 0` (from converting mult(b,a))
3. Main equation: `c - d = 0` (from the equality)

The Rabinowitsch trick on the negated assertion gives `(c-d)*e - 1 = 0`,
and the full system `{c - a*b, d - b*a, (c-d)*e - 1}` is provably UNSAT.

### Changes Required

1. **poly_extract.h**: Add `std::vector<polynomialt> side_equations` member
   and `std::size_t next_fresh = 0` counter.

2. **poly_extract.cpp**: In `to_polynomial()` for `ID_mult`, when both
   operands are non-constant, introduce a fresh variable and add the
   defining equation to `side_equations`. Return the fresh variable.

3. **boolbv.cpp** (`try_algebraic_solve`): After extracting equations,
   also include `extractor.side_equations` in the Gröbner basis input.

4. **Testing**: Verify on smt2_solver commutativity, associativity,
   distributivity benchmarks. Expected: <1ms for all.

### Expected Impact

All smt2 polynomial equation benchmarks solved in <1ms regardless of
bitwidth. The pre-scan multiplication count heuristic becomes
unnecessary for these benchmarks (Gröbner basis handles them directly).

### Alternative: Option B (not recommended)

Intercept equations from `boolbvt::convert_mult()` during bit-blasting.
More invasive, modifies existing code paths. Option A is preferred
because it's self-contained in poly_extractort (~20 lines).

## Level 2: Gröbner Bases for the Equational Fragment (IMPLEMENTED)

Implemented in `src/solvers/algebraic/`:
- `poly_ring.{h,cpp}`: Polynomial ring over Z_{2^d}, ~200 lines
- `groebner.{h,cpp}`: Strong Gröbner basis algorithm, ~250 lines
- `poly_extract.{h,cpp}`: Expression → polynomial conversion, ~150 lines

Integration: `boolbvt::set_to()` collects polynomial equations,
`boolbvt::finish_eager_conversion()` runs Gröbner basis. If UNSAT,
adds empty clause to SAT solver.

Results: commutativity BW=16-32 in 0.0002-0.0003s (31000x faster
than bit-blasting). Bitwidth-independent. Falls through to
bit-blasting for non-polynomial operations (XOR, shifts, inequalities).

Current limitation: only works in cbmc (SSA creates intermediate
variables). smt2_solver needs the inline expression decomposition
described in the "smt2_solver Algebraic Integration" section above.

### How Gröbner bases differ from subquadratic multiplication algorithms

Karatsuba, Toom-Cook, and Schönhage-Strassen are MULTIPLICATION
ALGORITHMS — they compute products. They produce circuits that are
then Tseitin-encoded into CNF. The algebraic structure is destroyed
by the encoding.

Gröbner bases are a DECISION PROCEDURE — they determine satisfiability
of polynomial equation systems. They work directly on the polynomial
ring Z_{2^N}[x1,...,xn], never creating propositional variables.

The NTT (Number Theoretic Transform) used by Schönhage-Strassen
COULD theoretically speed up polynomial multiplication within the
Gröbner basis computation, but for the bitwidths we care about
(8-32 bits), the polynomials are small enough that naive
multiplication is faster.

### References
- Song, Fu & Zhang 2024: arXiv:2402.16314
- Kaufmann & Biere 2021: AMulet2 (TACAS)
- Brain 2021: SMT Workshop, CEUR-WS Vol-2908

## Level 3: Hybrid Algebraic + Bit-Blasting

### What it would do
Decompose the formula into:
- Equational part (polynomial equations) → solve algebraically
- Residual part (inequalities, bitwise ops) → bit-blast with comba-cs

CEGAR loop:
1. Solve equational part algebraically
2. If UNSAT → done
3. If SAT → check algebraic solution against residual part
4. If residual violated → add violated constraint as equation, iterate

### Why this matters
Many real verification problems are MOSTLY algebraic with a few
bit-level constraints (e.g., overflow check on a multiplication
result). Neither pure algebraic methods nor pure bit-blasting
handles these well alone.

### Architecture
Maps onto CBMC's existing `--refine-arithmetic` framework:
- The algebraic solver replaces the weak initial approximation
- The bit-blasting solver handles the residual
- The CEGAR loop connects them

### Open questions
- How to efficiently extract the equational fragment from SSA?
- How to handle bitwise operations (AND, OR, XOR) in the polynomial ring?
  (Rabinowitsch trick: x AND y = x*y for single bits, but multi-bit
  AND requires bit-level decomposition)
- Performance: is the Gröbner basis computation fast enough to be
  worthwhile as a preprocessing step?
