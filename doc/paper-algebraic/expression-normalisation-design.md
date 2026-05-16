# Item 7 — Expression-level normalisation via the Gröbner basis

## Context

Martin's note (item 7 of Martin's review): "Reduce all polynomials,
including expressions, using the Gröbner basis. Less stupid than
adding ZFPs to the GB — use the GB as a normaliser for expressions
before bit-blasting." This bridges Martin's pithy framing
"Gröbner bases are working with equations, bit-blasting is working
with expressions": if the GB reduces every expression that goes to
bit-blasting, we get a richer composition.

## Current state of the algebraic / bit-blast handoff in CBMC

When `try_algebraic_solve` runs, it:
1. Extracts polynomial equations from SSA equalities.
2. Adds Rabinowitsch-augmented disequalities.
3. Optionally injects ZFP generators (from item 6 prototype).
4. Runs Buchberger (`strong_groebner_basist::compute`) with a 100k
   step budget.
5. If the basis contains a unit constant: returns UNSAT.
6. Otherwise (UNKNOWN), calls `extract_candidate` to look for
   univariate linear basis elements of the form `c*x + d = 0`
   where `c` is a unit; for each found, the candidate value
   `-d/c (mod 2^bw)` is wired as a SAT hint via gate literals.

The candidate extraction is the only existing bridge from the GB
back to the bit-blast layer. Everything else falls through with no
algebraic insight.

## What item 7 proposes

Generalise `extract_candidate` to handle **arbitrary polynomial
expressions**, not just univariate linear ones. The use cases:

### Use case A: constant-folding compound multiplications

After Buchberger, the basis may imply that a compound expression
like `a · b` evaluates to a known constant, even though neither `a`
nor `b` individually has a known value. Concretely: for each
multiplication `mult_exprt(lhs, rhs)` that was passed to the
algebraic layer:
1. Compute the polynomial form
   $p_{\textrm{lhs}} \cdot p_{\textrm{rhs}}$ via the polynomial
   extractor.
2. Reduce by the basis: $r := \mathrm{strong\_reduce}(p_{\textrm{lhs}}
   \cdot p_{\textrm{rhs}}, B)$.
3. If $r$ is a constant $c$: the multiplication's value is fixed
   modulo $2^d$. Emit a bit-level equality
   `mul_result == c` to guide SAT.
4. If $r$ is a single variable $y$ scaled by a unit: emit
   `mul_result == y` (after scaling).

### Use case B: discovered equalities between variables

For each pair of input symbols $(a, b)$ that appear in the
disequalities, compute $p_a - p_b$ and reduce by the basis. If it
reduces to 0, the GB has *implicitly proved* $a = b$. Emit a
bit-level equality between the two variables' bit-vectors.

This propagates ideal-membership-derived equalities to the
SAT/bit-blast layer, where they can constrain the search.

### Use case C: as a residual generator for fall-through

For each expression that survives to bit-blasting, run it through
the GB normaliser. If the normalised form is shorter (fewer
multiplications, lower degree, simpler structure) than the original,
prefer the normalised expression. This shrinks the bit-blast
encoding.

## Concrete CBMC integration point

In `boolbvt::try_algebraic_solve` (`src/solvers/flattening/boolbv.cpp`),
after `gb.compute(equations)` returns UNKNOWN and after
`extract_candidate` has run:

```cpp
if(std::getenv("ENABLE_GB_EXPR_NORMALISE"))
{
  // For each disequality (lhs != rhs), reduce both sides w.r.t. basis.
  // If reduction yields a constant or a known-shorter form, emit
  // SAT-level equality constraints to guide the bit-blast layer.

  for(const auto &diseq : algebraic_disequalities)
  {
    if(diseq.id() != ID_equal) continue;
    auto lhs = extractor.to_polynomial(to_equal_expr(diseq).lhs());
    auto rhs = extractor.to_polynomial(to_equal_expr(diseq).rhs());
    if(!lhs || !rhs) continue;

    polynomialt diff = *lhs - *rhs;
    polynomialt reduced =
      strong_groebner_basist::strong_reduce_external(diff, equations);

    // If reduced is constant 0, this is unsat (already caught upstream).
    // If reduced is constant c != 0, the disequality is necessarily
    // satisfied, so the SAT solver can skip exploring it.
    if(reduced.is_constant() && !reduced.is_zero())
    {
      // diseq always holds — assert lhs != rhs at SAT level (no-op).
      continue;
    }

    // If reduced is shorter (fewer terms) than the original, emit
    // a SAT-level equivalence: bv(lhs - rhs) == bv(reduced).
    if(reduced.terms.size() < diff.terms.size())
    {
      // Build expressiont for `reduced` and compare to original via
      // bit-vector equality. The SAT solver gets an extra clause set
      // that eliminates partial models inconsistent with the GB.
      ...
    }
  }
}
```

`strong_reduce_external` would need to be a public wrapper around
`strong_groebner_basist::strong_reduce` (currently private). Or
alternatively, a new free function `reduce_by_basis(p, B)` in
`groebner.{h,cpp}`.

## Subtleties

1. **What "shorter" means.** Term count is one metric; total degree,
   coefficient size, or total bits in the encoding could be others.
   Empirical tuning needed.
2. **Reduction cost.** Each reduction is at most O(|B| · |p|) in
   Buchberger's strong-reduce loop, but the constant factor matters.
   For benchmarks where the GB is small and expressions are simple,
   this is cheap. For pathological cases, reduction itself could
   take longer than bit-blasting.
3. **Correctness.** The reduced form is congruent to the original
   modulo the ideal $\langle B \rangle$, hence equal as a function on
   the variety of $B$. As a polynomial *equation*, the equivalence
   is conditional on $B$ holding. In CBMC's pipeline all SSA
   equalities hold by construction, so the reduction is sound.
4. **Interaction with the bit-blast cache.** The bit-blast layer
   memoises bit-vector encodings. Adding SAT-level equalities
   between bit-vectors that aren't already in the cache requires
   forcing materialisation. Care needed not to regress on benchmarks
   where the algebraic layer already does the right thing.

## Why this isn't trivially the same as `extract_candidate`

`extract_candidate` only finds **univariate linear** basis elements
$c \cdot x + d$ and emits a single value for $x$. The proposed
mechanism (a) reduces arbitrary polynomial expressions, not just
basis elements; (b) finds equalities of the form $p = q$ between
non-trivial polynomials; (c) communicates these as bit-vector
equalities, not single-variable assignments.

## Empirical hypothesis

On benchmarks where the algebraic layer currently returns UNKNOWN
(i.e., produces a non-trivial GB but doesn't find a unit constant)
and bit-blasting times out, expression-level GB normalisation will
either:

- **(a)** find a useful reduction that bit-blasting alone misses,
  recovering the benchmark; or
- **(b)** add overhead without changing solvability (negative
  result, but informative).

The benchmark categories most likely to benefit from (a):

- `mul_ineq_*` (multiplication monotonicity under no-overflow
  assumptions): the GB partially models the multiplication
  structure; reducing the comparison expressions w.r.t. the basis
  could shrink them.
- Martin's `correctness-*` benchmarks (encoding equivalence): each
  side is a polynomial; reducing one side w.r.t. the other's GB
  could expose equality.
- SMT-COMP queries with mixed polynomial / non-polynomial
  structure: the polynomial sub-fragment normalises, then the
  residual non-polynomial portion goes to bit-blast unchanged.

## Empirical evaluation (2026-05-16)

We implemented the simplest variant: post-Buchberger, for each
disequality `lhs != rhs` in `algebraic_disequalities`, reduce the
polynomial form `lhs - rhs` w.r.t.\ the global Gr\"obner basis. If
the reduction yields 0, the basis implies `lhs = rhs`, contradicting
the disequality. Behind `ENABLE_GB_EXPR_NORMALISE=1`. New static
method `strong_groebner_basist::reduce_by_basis` exposed in
`src/solvers/algebraic/groebner.{h,cpp}`.

### Results

**Custom suite (39 benchmarks):**

```
default      : 39/39
expr_norm    : 39/39   (no change)
```

Every benchmark has identical timing with and without expression
normalisation. The check fires (we verified by adding debug output)
but never finds a `diff` that reduces to 0 by the basis post-Buchberger.

**Martin's subpolynomial sample (210 benchmarks):**

```
default      : 119/210
expr_norm    : 119/210   (no change)
```

Zero benchmarks helped, zero benchmarks hurt. Total runtime difference
on commonly-solved benchmarks: $+0.04$ s (i.e., 0.0%) — well below noise.

### Why doesn't this variant fire?

The condition for item 7's check to find UNSAT is:
1. Per-disequality Buchberger with Rabinowitsch returned UNKNOWN.
2. Global Buchberger returned UNKNOWN.
3. Some disequality's `lhs - rhs` polynomial reduces to 0 by the
   global basis.

If condition 3 holds with the per-disequality basis (SSA equalities
$\cup$ {$(\textit{lhs} - \textit{rhs}) \cdot e - 1$}), then the
per-disequality Gröbner pass already returns UNSAT (the Rabinowitsch
polynomial reduces to $-1$, a unit constant). So condition 3 must
hold *only with the global basis* (which adds Rabinowitsch
polynomials for *other* disequalities).

This is rare in practice because CBMC's typical SMT query has a
single top-level disequality (the negated assertion). The
`algebraic_disequalities` vector usually has exactly one element,
so global basis = per-disequality basis, and the simple variant
provides no new reductions.

### What variant might work

The simple disequality-reduction variant is empirically null. More
sophisticated variants worth trying in future work:

1. **Compound multiplication constant folding.** For each
   `bvmul(a, b)` sub-expression that survives to bit-blasting,
   compute polynomial form and reduce by basis. If reduces to a
   constant, emit `bvmul = constant` at the SAT level.

2. **Pairwise variable equality discovery.** For each pair $(a, b)$
   of input symbols, reduce $a - b$ by basis. If 0, emit bit-vector
   equality between $a$ and $b$. Generally fires only when input
   symbols are constrained to be equal — uncommon in well-formed
   queries.

3. **Generalised candidate extraction.** Walk through every variable
   in the basis, not just univariate-linear ones; use
   reduce_by_basis to discover constants for compound monomials too.

Variants 1 and 3 require non-trivial engineering (polynomial-to-expr
conversion, walking the basis structure). Variant 2 is simple but
unlikely to fire empirically.

## Conclusion (2026-05-16)

The simplest variant of item 7 (post-Buchberger disequality
reduction) is **empirically null** on both the custom suite and
Martin's subpolynomial sample. The CBMC pipeline's per-disequality
Rabinowitsch + Gröbner pass already catches what this variant
could catch.

A useful variant of item 7 would need to operate on compound
expressions or pairs of variables, not on the disequality
polynomials directly. This remains a research direction.

## Implementation effort estimate

- 1-2 days: implementation + initial empirical validation.
- 1 week: full ablation across the 5-pool comparison framework
  used elsewhere in this repo.
- 2 weeks: tuning of "shorter than" heuristics and integration with
  the bit-blast cache.

## Deferred

For now this is documented as a research direction. A small prototype
in `src/solvers/flattening/boolbv.cpp` behind
`ENABLE_GB_EXPR_NORMALISE` would be the next step.

## Future work pointer

Once Paper 2 is submitted, the natural follow-up paper combines
items 7 and 8 (this document and `bit-level-polynomial-design.md`)
into a full theory-solver architecture for bit-vector arithmetic.
The pitch: "the algebraic layer becomes a true theory solver,
exchanging arbitrary polynomial information with the bit-blast
layer in both directions."
