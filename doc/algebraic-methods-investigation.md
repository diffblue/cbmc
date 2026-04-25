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

## Level 3: Hybrid Algebraic + Bit-Blasting (Detailed Plan)

### Motivation

Levels 1-2 handle pure polynomial equations. Level 4 (bit-blasting)
handles everything else. But some problems are MIXED: mostly polynomial
with a few non-polynomial constraints. Examples:

```
// Overflow-safe commutativity: polynomial + inequality
assert(a * b == b * a);          // polynomial (Gröbner solves)
assert(a * b <= MAX_UINT16);     // inequality (needs bit-blasting)

// Hash with algebraic property: polynomial + XOR
uint16_t h = key * data;         // polynomial
h ^= h >> 8;                     // XOR + shift (non-polynomial)
assert(f(key, data) == f(key, data));  // determinism
```

Currently, the Gröbner basis ignores the inequality/XOR and returns
UNKNOWN. The bit-blasting then solves the entire problem from scratch,
not benefiting from the algebraic structure at all.

### Architecture: CEGAR via `bv_refinementt`

Level 3 extends the existing `bv_refinementt` CEGAR loop:

```
                    ┌─────────────────────┐
                    │ Polynomial Extractor │
                    │ (separate equational │
                    │  and residual parts) │
                    └──────┬──────────────┘
                           │
              ┌────────────┴────────────┐
              │                         │
    ┌─────────▼─────────┐   ┌──────────▼──────────┐
    │ Gröbner Basis      │   │ Residual Constraints │
    │ (equational part)  │   │ (inequalities, XOR,  │
    │                    │   │  shifts, etc.)        │
    └─────────┬─────────┘   └──────────┬──────────┘
              │                         │
              │ SAT → candidate         │
              │ assignment              │
              │                         │
              ▼                         ▼
    ┌─────────────────────────────────────────────┐
    │ Check candidate against residual via SAT    │
    │ (bit-blast only the residual constraints    │
    │  with the algebraic variables fixed)        │
    └──────────────────┬──────────────────────────┘
                       │
              ┌────────┴────────┐
              │                 │
         consistent         violated
              │                 │
              ▼                 ▼
           RESULT          Add violated constraint
           (SAT/UNSAT)     as polynomial equation,
                           re-run Gröbner basis
```

### Implementation Steps

#### Step 1: Extract candidate assignment from Gröbner basis

When the Gröbner basis returns UNKNOWN (not UNSAT), the reduced
basis represents the set of solutions. For simple cases (linear
equations), we can read off a candidate assignment directly.

**File:** `src/solvers/algebraic/groebner.h`

```cpp
class strong_groebner_basist {
public:
  // ... existing ...

  /// After compute() returns UNKNOWN, try to extract a candidate
  /// assignment for the variables. Returns empty map if no
  /// assignment can be extracted.
  std::map<std::size_t, mp_integer>
  extract_candidate(const std::vector<polynomialt> &basis, unsigned bw);
};
```

**Algorithm:** Walk the basis looking for univariate polynomials
(polynomials in a single variable). For each `c*x + d = 0`, extract
`x = -d/c mod 2^bw`. For multivariate polynomials, substitute
already-determined variables and repeat.

This is a best-effort extraction — it may not find a complete
assignment. If it can't, fall through to bit-blasting.

**Estimated:** ~50 lines.

#### Step 2: Check candidate against residual constraints

The residual constraints (inequalities, bitwise ops) are already
in the SAT solver from `boolbvt::set_to()`. We need to check if
the candidate assignment satisfies them.

**Integration point:** `bv_refinementt::check_SAT()`

The existing CEGAR loop already does this: after `prop_solve()`
returns SAT, `check_SAT()` verifies the assignment against the
approximated operations. We extend this to also verify against
the algebraic candidate.

**Approach:** Before the first `prop_solve()` call, if the Gröbner
basis extracted a candidate, add it as assumptions to the SAT solver:

```cpp
// In bv_refinementt::dec_solve(), after try_algebraic_solve():
if(algebraic_candidate.has_value()) {
  // For each variable x_i = v_i in the candidate:
  // Add assumption: x_i == v_i (as a SAT assumption, retractable)
  for(auto &[var_idx, value] : *algebraic_candidate) {
    // Find the corresponding bit-vector in the SAT solver
    // and add equality constraints as assumptions
  }
}
```

If the SAT solver returns SAT with these assumptions, the candidate
is consistent with the residual — we have a genuine SAT result.

If the SAT solver returns UNSAT (the candidate violates the residual),
the conflict clause tells us which residual constraint was violated.
We can then:
1. Remove the assumptions
2. Add the violated constraint as a polynomial equation (if possible)
3. Re-run the Gröbner basis with the additional equation
4. Repeat

**Estimated:** ~100 lines.

#### Step 3: Convert residual violations to polynomial equations

When the SAT solver finds that the algebraic candidate violates a
residual constraint, we need to convert that constraint to a
polynomial equation (if possible) and add it to the Gröbner basis.

**What can be converted:**
- `a > b` → `a - b - 1 >= 0` → introduce slack variable s:
  `a - b - 1 - s = 0` with `s >= 0` (partial — the non-negativity
  of s still needs bit-blasting)
- `a & b == c` → for single bits: `a*b - c = 0` (exact)
  For multi-bit: decompose into per-bit equations (expensive)

**What cannot be converted:**
- Shifts by variable amounts
- Division
- Complex control flow

**Practical approach:** Only convert simple inequalities and
single-bit bitwise operations. For everything else, fall through
to full bit-blasting.

**Estimated:** ~80 lines.

#### Step 4: Integration into `bv_refinementt`

Modify `bv_refinementt::dec_solve()`:

```cpp
resultt bv_refinementt::dec_solve(const exprt &assumption) {
  finish_eager_conversion();

  // Level 2: try pure algebraic solving
  auto algebraic_result = try_algebraic_solve();
  if(algebraic_result == resultt::D_UNSATISFIABLE)
    return resultt::D_UNSATISFIABLE;

  // Level 3: if Gröbner basis returned UNKNOWN with a candidate,
  // try the candidate against the residual constraints
  if(algebraic_candidate.has_value()) {
    // Add candidate as SAT assumptions
    add_algebraic_assumptions(*algebraic_candidate);

    switch(prop_solve()) {
    case resultt::D_SATISFIABLE:
      // Candidate is consistent with residual — genuine SAT
      check_SAT();
      if(!progress)
        return resultt::D_SATISFIABLE;
      // Spurious — fall through to normal CEGAR
      break;
    case resultt::D_UNSATISFIABLE:
      // Candidate violates residual — extract conflict,
      // add as polynomial equation, re-run Gröbner basis
      retract_algebraic_assumptions();
      if(refine_from_conflict()) {
        // Re-run Gröbner basis with additional equation
        algebraic_result = try_algebraic_solve();
        if(algebraic_result == resultt::D_UNSATISFIABLE)
          return resultt::D_UNSATISFIABLE;
      }
      break;
    }
  }

  // Fall through to normal CEGAR loop
  // ... existing code ...
}
```

**Estimated:** ~80 lines of integration code.

### Variable Mapping Challenge

The main engineering challenge: mapping between polynomial variables
(indices in the Gröbner basis) and SAT variables (bit-vectors in
the SAT solver). The `poly_extractort` maintains a `var_map` from
symbol names to polynomial indices. We need the reverse mapping:
from polynomial indices to the bit-vectors in `boolbvt`.

**Solution:** Store the reverse mapping in `poly_extractort`:

```cpp
// In poly_extractort:
std::map<std::size_t, irep_idt> reverse_var_map;
// Populated in get_var_index()
```

Then in the integration code, use `boolbvt::convert_bv()` to get
the bit-vector for each symbol and add equality constraints.

### Expected Performance

For pure polynomial problems: no change (Gröbner basis solves them
at Level 2, Level 3 is never reached).

For mixed problems (polynomial + inequality):
- Best case: Gröbner basis extracts a candidate that satisfies the
  residual on the first try → one SAT call with assumptions (fast)
- Typical case: 1-3 CEGAR iterations before convergence
- Worst case: falls through to full bit-blasting (no regression)

### Testing Strategy

1. **Pure polynomial:** verify Level 2 still works (no regression)
2. **Pure non-polynomial:** verify fall-through works (no regression)
3. **Mixed:** new benchmarks:
   - `a*b == b*a && a > 100` (polynomial + inequality)
   - `a*b == b*a && (a & 0xFF) == a` (polynomial + bitwise)
   - `a*(b+c) == a*b + a*c && a*b < 1000` (distributivity + inequality)

### Estimated Total: ~310 lines of new code

- Step 1 (candidate extraction): ~50 lines
- Step 2 (residual checking): ~100 lines
- Step 3 (conflict conversion): ~80 lines
- Step 4 (integration): ~80 lines

### Dependencies

- Phases 1-4 (all implemented)
- `bv_refinementt` CEGAR infrastructure (existing)
- Reverse variable mapping (new, ~20 lines)

### Risk Assessment

- **Low risk:** Steps 1-2 (candidate extraction and checking) are
  straightforward extensions of existing infrastructure
- **Medium risk:** Step 3 (conflict conversion) is limited by what
  constraints can be polynomialized — many can't
- **High risk:** The CEGAR loop may not converge for complex mixed
  problems — but the fallback to full bit-blasting ensures correctness
