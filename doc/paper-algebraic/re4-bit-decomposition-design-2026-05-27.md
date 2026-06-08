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

### Empirical findings (2026-05-27, post-MVP)

The MVP has been tested on a range of synthetic queries
exercising bit-decomposition. Summary:

| Query | Bitwidth | Bit-decomp count | Time (algebraic) | Time (bit-blast only) |
|---|---|---|---|---|
| `(2x)>>1 = x ∧ x < 8` | 4 | 1 | 0.06 s | 0.00 s |
| `(2a)>>1 = a ∧ a < 128` | 8 | 1 | 0.51 s | 0.00 s |
| `((a+b)>>1) = ((b+a)>>1)` | 16 | 2 (compound) | T/O 30 s | 0.00 s |
| `a & 0 = 0` | 4 | 1 | 0.07 s | 0.00 s |
| `a | 0 = a` | 4 | 1 | (bit-blast first) | 0.00 s |
| `a XOR a = 0` | 4 | (cached share) | 0.00 s | 0.00 s |
| `(a XOR b) XOR b = a` | 4 | 2 + compound | T/O 30 s | (n/a) |
| `~~a = a` | 4 | 2 (a, then ~a host) | 8.55 s | (n/a) |
| `a & a = a` | 4 | 1 (cached share) | 0.00 s | 0.00 s |
| `~(a & b) = ~a | ~b` | 4 | 4 (compound) | 4.16 s | (n/a) |

All UNSAT cases are answered correctly. The MVP is sound. Where
the algebraic path is faster than bit-blasting: never (bit-blast
is always 0.00 s on these tiny queries). Where the algebraic
path takes seconds or times out: any compound bit-decomposition
where the algebra has to derive the equality through Buchberger.

**Diagnosis.** Bit-decomposition adds substantial Buchberger cost
through three mechanisms:

1. **Many degree-2 generators.** Each decomposed integer adds $d$
   idempotency relations $b_i^2 - b_i = 0$. With $d = 16$ and 4
   decomposed integers, that's 64 degree-2 generators. S-polynomial
   computation between every pair grows quadratically in their
   count.

2. **Polynomial expansion in compound expressions.** When a
   partial operator (e.g., bvlshr) is applied to a compound
   expression like $(a + b)$, the encoding introduces a fresh host
   variable $h$ with the equation $h - a - b = 0$ and decomposes
   $h$ separately. Two syntactically-different-but-semantically-
   equal compounds (like $a + b$ and $b + a$) get distinct hosts
   with distinct bit decompositions; Buchberger then has to derive
   $h_1 = h_2$ by reducing through the $a, b$ structure, multiplied
   across all bit positions. The S-polynomial work is quadratic in
   the bit count.

3. **Incomplete cancellation.** Idempotency $b^2 = b$ is a strong
   reduction rule, but our `strong_reduce` doesn't exploit it
   specially — it treats $b^2 - b$ as a generic polynomial. A
   Frobenius-aware reduction step would shortcut these reductions
   significantly.

**Implication.** The MVP unblocks the *soundness* concern that
killed the flag-gated approach (the procedure is now sound by
construction, no opt-in, no over-refutation). But the *performance*
ceiling on bit-decomposition-heavy queries is low; production-scale
applications (faithful Toom-4 SABER, GRS-128, complex relational
queries) need either:

- **a custom Buchberger reduction strategy** that recognises and
  fast-paths idempotency, OR
- **a different procedure architecture** for bit-decomposed bases
  (e.g., DPLL(B) where bit-blasting handles the bit relations and
  the algebraic procedure handles the integer relations, exchanging
  via shared variables).

Estimated effort for a custom reduction strategy: 1–2 weeks of
focused work. The Frobenius observation
($b^2 = b \Rightarrow b^k = b$ for $k \geq 1$) suggests a simple
optimization: when reducing a polynomial $f$, immediately replace
$b^k$ with $b$ for any decomposed $b$ before any S-polynomial
computation. This converts the basis from "many high-degree
relations" to "many degree-1 polynomials over Boolean variables",
which Buchberger should handle vastly faster.

This is the next sub-goal-3 step: prototype Frobenius-aware
reduction and re-measure the queries above.

### Sub-goal 3 progress (2026-05-27, post-Frobenius)

Three orthogonal optimisations applied (in order):

**(a) Frobenius-aware reduction in Buchberger** (commit
`d864305fbd`). Bit variables satisfy $b^2 = b$, so $b^k = b$
for $k \geq 1$. Adding a step in `s_polynomial`,
`strong_reduce`, and the 2-multiple step that clamps bit-
variable exponents to 1 immediately after each polynomial
operation gives 70–1000× speedup on bit-decomp queries that
solve via incremental idempotency reduction.

**(b) Structural bit-decomposition** (commit `61faaf0f29`,
part 1 of 2). Refactor `decompose_bits()` to recursively
compute bit polynomials directly for recognised bit-operations
(`bvnot`, `bvshl`, `bvlshr`, `bvand`, `bvor`, `bvxor`,
constants), without going through a fresh host. Eager
Frobenius applied during construction keeps intermediate
polynomials small.

**(c) Polynomial-form host cache** (commit `61faaf0f29`,
part 2 of 2). Two syntactically-different-but-semantically-
equal compound expressions like $(a + b)$ and $(b + a)$
normalise to the same polynomial. Without caching, each gets
a distinct host with a distinct bit decomposition; with the
new cache, they share a host. This eliminates a major class
of redundant Buchberger work.

**Combined effect:**

| Query | Bitwidth | Pre-Frobenius | Post-(a)+(b)+(c) |
|---|---|---|---|
| `((a+b)>>1) = ((b+a)>>1)` | 16 | T/O 30 s | 0.00 s |
| `((a+b)>>1) = ((b+a)>>1)` | 32 | T/O 30 s | 0.00 s |
| `~(a & b) = ~a | ~b` (De Morgan) | 16 | T/O 30 s | 0.00 s |
| `(a XOR b) XOR b = a` | 8 | T/O 30 s | 0.01 s |
| `(a XOR b) XOR b = a` | 16 | T/O 30 s | 0.70 s |
| `~~a = a` | 4 | 8.55 s | 0.00 s |
| `((a+b)-(a-b))>>1 = b ∧ b<128` (8-bit) | 8 | (untested) | 0.04 s |
| `((a+b)+(c+d))>>2 = ((a+c)+(b+d))>>2` | 16 | (untested) | 0.00 s |

The last two queries are Toom-Cook-style identities — verifying
that two algebraic re-arrangements with shifts produce identical
results. These now decide cleanly, suggesting Re 4 sub-goals 4
(faithful Toom-Cook 4-way SABER) is now reachable.

**Remaining wall.** `bvxor` cancellation at 24+ bits still
times out. The cost is in the polynomial multiplications during
deeply-nested bit combination: bvxor expands each bit to a
polynomial with degree-2 cross-terms, and chained xor multiplies
these. Even with eager Frobenius, the term count grows. Further
optimisation candidates (estimated 1–3 weeks each):

- **Inline simplification during construction.** Apply $b_i^2
  \to b_i$ during the polynomial multiplication operator, not
  just after. Keeps intermediate term counts smaller.
- **Linear elimination of host variables.** Sum-decomposition
  $h - \sum_i 2^i b_i = 0$ is a degree-1 equation with $h$ as
  leading term in lex order; using it as a substitution rule
  eliminates $h$ everywhere it appears.
- **Custom orderings.** Place bit variables and host variables
  in the variable order to make Buchberger's reductions more
  predictable.

The remaining wall does not block Re 4 sub-goals 4 and 5 (faithful
Toom-Cook 4-way SABER and GRS-128) — those exercise compound
shifts on linear combinations, which now solve cleanly. Sub-goal
6 (universal-relational queries with `bvult` / `bvslt`) is a
separate encoding question still to be designed.

### Sub-goal 3 final wins (2026-05-27, post-linear-elimination)

Two further optimisations applied:

**(d) Inline idempotency simplification in polynomial multiplication**
(commit `50252003e4`). New `polynomialt::multiply(other,
bit_vars)` clamps bit-variable exponents to 1 during the term-
pair loop, avoiding materialisation of $b^2$ terms that would
then be reduced. Empirical impact on the test suite: neutral
(the bottleneck wasn't here). Kept as a clean infrastructure
improvement.

**(e) Linear elimination of host variables via substitution**
(commit `a54fa27f04`). Substitutes each host variable $h$ with
its bit-sum polynomial $\sum_i 2^i b_i$ in every polynomial of
the basis BEFORE Buchberger and BEFORE the vanishing-polynomial
test.

The bottleneck was actually the **vanishing-polynomial test** on
bit-decomp queries, not Buchberger. The vanishing test builds a
Kronecker product over all variables; with both host $h$ and
bit variables $b_i$ in the polynomial, the Kronecker product
size grows exponentially in the bit count.

With linear elimination, the diff polynomial collapses to zero
immediately for queries like bvxor cancellation, the vanishing
test recognises the trivial vanishing case, and we report UNSAT
without any heavy computation.

**Final empirical results:**

| Query | bw | Before (a)(b)(c) | After (a)(b)(c)(d)(e) |
|---|---|---|---|
| `(a XOR b) XOR b = a` | 4 | 0.00 s | 0.00 s |
| `(a XOR b) XOR b = a` | 16 | 0.70 s | **0.00 s** |
| `(a XOR b) XOR b = a` | 24 | T/O 30 s | **0.00 s** |
| `(a XOR b) XOR b = a` | 32 | T/O 30 s | **0.01 s** |
| `(a XOR b) XOR b = a` | 64 | (untested) | **0.02 s** |
| `(a XOR b) XOR b = a` | 128 | (untested) | **0.07 s** |
| De Morgan | 128 | (untested) | **0.08 s** |

**Linear scaling** in bitwidth, ~$O(d)$ on these queries.
Re 4 sub-goal 3 is essentially complete: the algebraic procedure
with bit-decomposition is tractable on production-scale bitwidths
for queries with reasonable polynomial structure.

**Remaining work:**

- Re 4 sub-goal 4: faithful Toom-Cook 4-way SABER generator.
- Re 4 sub-goal 5: GRS-128 community benchmark.
- Re 4 sub-goal 6: universal-relational queries (`bvult`,
  `bvslt`) — separate encoding design.

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
