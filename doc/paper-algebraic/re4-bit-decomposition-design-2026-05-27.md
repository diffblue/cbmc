# Re 4: Bit-Decomposition Variables — Design

*Date: 2026-05-27*
*Status: design + MVP implementation in flight on `features/adder`.*
*Scope: this design covers the MVP (sub-goals 1, 2, partial 3 of
`future-directions-2026-05-27.md`). Sub-goals 4–6 are
applications and follow once the MVP works.*

## Goal

Make the algebraic procedure sound on queries containing partial
bit-vector operations (`bvlshr`, `bvand`, `bvor`, `bvxor`,
relational predicates `bvult`/`bvslt`).

The core idea: introduce auxiliary bit variables
$b_{a,i} \in \{0, 1\}$ and add the constraints

- **idempotency**: $b_{a,i}^2 = b_{a,i}$ for each $i$, equivalently
  $b_{a,i}^2 - b_{a,i} = 0$;
- **sum-decomposition**: $a = \sum_{i = 0}^{d-1} 2^i b_{a,i}$,
  equivalently $a - \sum_i 2^i b_{a,i} = 0$.

These constraints uniquely identify $b_{a,i}$ as the $i$-th bit of
$a$ in $\mathbb{Z}_{2^d}$. Idempotency forces
$b_{a,i} \in \{0, 1\}$ (in $\mathbb{Z}_{2^d}$, $b(b - 1) \equiv 0$
implies $b \equiv 0$ or $b \equiv 1$ since $b$ and $b - 1$ are
coprime); sum-decomposition then forces the unique bit assignment.

With bit variables in hand, partial bit-vector operations become
sound polynomial expressions:

- $a \gg k = \sum_{i = k}^{d-1} 2^{i-k} b_{a,i}$.
- $\mathit{bvand}(a, b) = \sum_i 2^i (b_{a,i} \cdot b_{b,i})$.
- $\mathit{bvor}(a, b) = \sum_i 2^i (b_{a,i} + b_{b,i} - b_{a,i} \cdot b_{b,i})$.
- $\mathit{bvxor}(a, b) = \sum_i 2^i (b_{a,i} + b_{b,i} - 2 b_{a,i} \cdot b_{b,i})$.
- $\mathit{bvnot}(a) = \sum_i 2^i (1 - b_{a,i})$.

These hold in $\mathbb{Z}_{2^d}$ (the host ring). Arithmetic on
$b_{a,i}$ stays within the ring; the result is recombined with
power-of-two coefficients.

For relational predicates (`bvult`, `bvslt`), the encoding is more
involved (one introduces a comparison-result bit and constraints
linking it to the bit decomposition of both operands); deferred to
sub-goal 6, not in the MVP.

## Architecture

### Where bit-decomposition happens

In `src/solvers/algebraic/poly_extract.cpp`. The `to_polynomial`
method gains a new helper `decompose_bits(e)` that:

1. Recursively converts `e` to a polynomial $p$ via the existing
   `to_polynomial` machinery.
2. If $p$ is a single variable $x_v$ already in the bit-decomposition
   cache, returns the cached vector of bit-variable polynomials.
3. Otherwise:
   - Introduces a fresh "host" variable $h$ (already done by the
     existing `__fresh_mul_N` infrastructure when needed) — or
     reuses $x_v$ directly if $p$ is a single variable.
   - Allocates $d$ fresh bit-variable indices $b_0, \ldots, b_{d-1}$,
     where $d$ is the polynomial bitwidth.
   - For each $i$, adds the idempotency side equation
     $b_i^2 - b_i = 0$.
   - Adds the sum-decomposition side equation
     $h - \sum_i 2^i b_i = 0$.
   - Caches the bit-variable list keyed by $h$'s variable index.
   - Returns the bit polynomials $[b_0, \ldots, b_{d-1}]$.

The new `to_polynomial` cases for partial operators call
`decompose_bits` on their operand(s) and combine the results into
a polynomial expression using the formulas above.

### Caching

Without caching, the same variable could be decomposed multiple
times — once per partial operator that uses it — leading to
duplicate idempotency constraints (harmless for correctness,
costly for Buchberger).

Cache key: the polynomial-variable index $v$ (the value returned
by `get_var_index(name)`). Cache value: `std::vector<std::size_t>`
holding the bit-variable indices $b_0, \ldots, b_{d-1}$ for
variable $v$.

When decomposing a non-leaf expression (e.g., `bvlshr (a + b) 1`),
we introduce a fresh "host" variable for the polynomial, equate it
with the polynomial via a side equation, and decompose the host.
This means the host gets a single bit-decomposition shared across
all uses of `bvlshr (a + b)` syntactically appearing the same way.
Common subexpression sharing across syntactically different
expressions that compute the same value is left to Buchberger.

### Naming convention

- Host variable for compound expressions (when needed):
  `__bd_host_<n>` where `<n>` is a counter.
- Bit variables for polynomial variable $v$:
  `__bd_bit_<v>_<i>` for $i = 0, \ldots, d-1$.

This makes side equations recognisable in debug output.

### Soundness

By construction, the encoding is sound: the constraints
*uniquely determine* the bit variables given the host variable's
value. So any model of the augmented system corresponds to exactly
one model of the original (with the bit values determined by the
host) and vice versa. The procedure neither over-refutes
(correct UNSAT-only) nor under-refutes (no spurious SATs).

The encoding doesn't change SAT/UNSAT status of the formula: it
only adds constraints whose solutions are uniquely determined by
the existing variables. Hence the procedure is sound by default;
no opt-in flag is needed.

## Sub-goals 1 and 2: MVP scope

This document scopes the MVP (sub-goals 1 and 2):

1. **On-demand bit-decomposition entry point** in `poly_extract.cpp`:
   - New private map `bit_decomp_cache` keyed by var index.
   - New helper `decompose_bits(e) -> std::optional<std::vector<polynomialt>>`.
2. **Polynomial encoding of `bvlshr`**:
   - New `ID_lshr` case in `to_polynomial` that calls
     `decompose_bits` and assembles the right-shift polynomial.
3. **Tests**:
   - Synthetic shift identity (sound positive case).
   - The over-refute case from before (formula with `x>>1=5` and
     `x!=10`) — now correctly answered.
   - Existing benchmarks regression (build + sample of Martin
     subpoly + SABER scaling N=4..64).

`bvand` / `bvor` / `bvxor` / `bvnot` are stretch goals in the same
session if time permits — they share the `decompose_bits`
infrastructure and add a few more `to_polynomial` cases.

## Sub-goal 3 (deferred): Buchberger tractability at scale

Sanity check at $d = 4$ with one decomposed variable
(`saber/sanity-bit-decomp.smt2`) passed in 0.00 s. The MVP will be
tested at $d = 16$ on the SABER scale to assess whether
bit-decomposition is tractable at production parameters.

The empirical question: how does Buchberger handle a basis with
$d$ idempotency constraints + 1 sum-decomposition constraint per
decomposed variable?

- Idempotency $b^2 - b = 0$ has degree 2; it's a "Frobenius"-like
  relation that reduces $b^k$ to $b$ for $k \geq 1$.
- Sum-decomposition $h - \sum 2^i b_i = 0$ has degree 1; it
  expresses $h$ in terms of the $b_i$.

In principle, Buchberger should "handle" these efficiently because
- idempotency reductions kill high-degree terms in $b_i$ quickly;
- sum-decomposition is a linear relation usable for substitution.

But $d = 16$ means 16 bit variables per decomposed integer; SABER
N=16 has $2N = 32$ input variables, so worst-case 32 × 16 = 512
bit variables and 32 × 17 = 544 added constraints. This is a
non-trivial increase. The empirical measurement is necessary
before committing to bit-decomposition for SABER-scale queries.

If tractable: Re 4 unlocks faithful Toom-4 SABER and the
relational classes.

If intractable: design an "on-demand by partial-operator" mode
where only variables that appear directly under a partial operator
get decomposed (vs. eager decomposition of all input variables).
This is the natural fallback.

## Sub-goals 4–6 (deferred to follow-on sessions)

- **Sub-goal 4** (faithful Toom-Cook 4-way SABER): write
  `make-saber-query.py --algo-b toom4` mode emitting SABER's
  actual interpolation formulas with `>> 1` and `>> 3`. Time
  against schoolbook.
- **Sub-goal 5** (GRS-128 community benchmark): locate in SMT-LIB,
  test whether Re 4 + existing procedure unlocks it.
- **Sub-goal 6** (universal-relational class): add `bvult` / `bvslt`
  encodings and a few queries demonstrating universal-relational
  decidability (e.g., $\forall a, b.\ a < b \implies a + 1 \leq b$).

## Risks

- **Tractability**: addressed by sub-goal 3's empirical
  measurement.
- **Soundness**: by construction, the encoding is sound (no opt-in
  flag, no over-refutation possible). The previous flag-gated
  attempt's worked counter-example ($d=4$, $c=9$: $2c \bmod 16 = 2$,
  $(2c) \gg 1 = 1$, polynomial form "$c$" yields $9$) does *not*
  apply to the bit-decomposition encoding because the bit
  variables capture all 4 bits exactly — no lost information.
- **Performance regression on non-bvlshr benchmarks**: the new
  code path only fires when an `ID_lshr` is encountered. Existing
  benchmarks without `bvlshr` are unaffected.
- **Performance regression on benchmarks where `bvlshr` was
  previously handled by bit-blasting**: now the algebraic path
  attempts bit-decomposition first. If it fails (e.g., Buchberger
  times out), the assertion's status may still resolve via
  bit-blasting, but with slower overall runtime due to the failed
  algebraic attempt. This is acceptable for the MVP; future work
  may add heuristics to skip bit-decomposition when the polynomial
  form is unlikely to help.

## Implementation steps in this session

1. Add `bit_decomp_cache` map and `decompose_bits` helper to
   `poly_extract.{h,cpp}`.
2. Add `ID_lshr` case in `to_polynomial`.
3. Test:
   - synthetic positive cases (e.g., `(2x) >> 1 = x` for x < 2^{d-1});
   - the over-refute case (formula with `(bvlshr x 1) = 5` and
     `x != 10`) — should now correctly be SAT;
   - existing regression sample.
4. Test on SABER N=16 to confirm no regression.
5. Commit MVP.

Stretch (this session if time permits):

6. Add `ID_bitand` / `ID_bitor` / `ID_bitxor` / `ID_bitnot`.
7. Generate Toom-Cook-3 (simpler than Toom-4) SABER variant
   with shifts and try it.

If stretch goals don't fit, they go on the Re 4 follow-on list.

## Cross-references

- `future-directions-2026-05-27.md` — master tracker; this doc
  is the design for Re 4's MVP.
- `saber-experiment-2026-05-26.md` — Re 4 sanity check at $d = 4$.
- `bit-level-polynomial-design.md` — earlier (2026-05-16) design
  notes, partly subsumed.
- `src/solvers/algebraic/poly_extract.{h,cpp}` — implementation
  target.
- `src/solvers/flattening/boolbv.cpp::try_algebraic_solve` — the
  algebraic pre-solver entry point that reads `side_equations`.
