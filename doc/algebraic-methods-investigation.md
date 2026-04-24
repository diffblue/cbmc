# Algebraic Methods for Bit-Vector Verification

## Status: Future Work (tracking document)

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

## Level 2: Gröbner Bases for the Equational Fragment

### What it would do
Given a set of polynomial equations over Z_{2^N}, compute a strong
Gröbner basis and check if 1 is in the ideal (UNSAT). This would
handle the intermediate-variable case: `c - a*b = 0, d - b*a = 0,
c - d ≠ 0` reduces to `{1 = 0}` algebraically.

### How it differs from subquadratic multiplication algorithms
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

### Implementation approach
1. Before bit-blasting, extract polynomial equations from the SSA
2. Compute strong Gröbner basis over Z_{2^d} (Song et al. 2024 algorithm)
3. If basis contains a constant → UNSAT (no bit-blasting needed)
4. If not → fall through to bit-blasting with comba-cs

### Integration point
- New preprocessing pass in `goto-symex` or `boolbvt`
- Or extend `bv_refinementt` to use Gröbner basis as the initial
  approximation (instead of x*0=0, x*1=x)

### Dependencies
- Polynomial arithmetic library over Z_{2^d}
- Strong Gröbner basis algorithm (Song et al., ~200 lines core)
- Extended Euclidean algorithm for multiplicative inverse mod 2^d

### References
- Song, Fu & Zhang 2024: "Equational Bit-Vector Solving via Strong
  Gröbner Bases" (arXiv:2402.16314)
- Kaufmann & Biere 2021: AMulet2 (Gröbner bases for circuit verification)
- Brain 2021: "Further Steps Down The Wrong Path" (SMT Workshop)

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
