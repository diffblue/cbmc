# Item 8 — Bit-level partial information as polynomial constraints

## Context

Martin's note (item 8 of the review): represent partial bit-level
information (e.g.\ "the 3rd bit of $x$ is 1", "the 7th bit of
$3x^7 - 5y$ is 0") as polynomial constraints. Do "actual theory
solver stuff" — i.e., let the algebraic layer exchange information
with the SAT layer at the bit level, not just at the
arithmetic-value level.

Combined with item 7 (expression normalisation), this would close
the loop: the algebraic layer would be a full theory solver,
sending and receiving polynomial constraints during the SAT
search.

## The fundamental challenge: polynomial encoding of bit operations

In $\mathbb{Z}_{2^d}$, the "$i$-th bit of $x$" is the function
$\mathrm{bit}_i(x) := \lfloor x / 2^i \rfloor \bmod 2$.

This is **not** a polynomial in $x$. The integer-division and
modular-reduction operations have no closed-form polynomial
expression in $\mathbb{Z}_{2^d}[x]$.

To make bit-level information polynomial, we must introduce
**fresh variables for individual bits** and tie them to $x$ via
an extra equation. Two natural encodings:

### Encoding A: bit-decomposition variables

For each input variable $x$ of bitwidth $d$, introduce $d$ fresh
boolean-like variables $b_{x,0}, b_{x,1}, \ldots, b_{x,d-1}$ over
$\mathbb{Z}_{2^d}$, with the side equations:

\begin{align*}
  x &= \sum_{i=0}^{d-1} 2^i \cdot b_{x,i} \\
  b_{x,i}^2 &= b_{x,i} \quad \text{for each } i  \quad\text{(idempotency)}
\end{align*}

The idempotency equations $b^2 = b$ force each $b_{x,i}$ to be 0
or 1 modulo any $2^k$. Over $\mathbb{Z}_{2^d}$, the solutions to
$b^2 = b$ are exactly $b \in \{0, 1\}$ (provided $b$ is in the
canonical residue range $\{0, \ldots, 2^d - 1\}$).

A bit-level fact "$\mathrm{bit}_3(x) = 1$" becomes the polynomial
equation $b_{x,3} - 1 = 0$, which the GB can absorb. A fact
about a derived expression like
"$\mathrm{bit}_7(3x^7 - 5y) = 0$" requires representing
$3x^7 - 5y$'s bit-decomposition variables too — see §"Inferred
bit variables for expressions" below.

### Encoding B: boolean-variable embedding

A more elaborate encoding works over a larger ring: $\mathbb{Z}_{2^d}$
for the arithmetic plus some carrier for the bits. Lifting all
arithmetic to a Boolean polynomial ring $\mathbb{F}_2[b_{x,0},
\ldots]$ recovers full bit-level reasoning but loses the structural
benefit of working with $\mathbb{Z}_{2^d}$. This is essentially what
Amulet2~\cite{kaufmann2021amulet} does at the AIG level.

We focus on encoding A: keep the algebraic layer over
$\mathbb{Z}_{2^d}$ and add a bit-decomposition sub-layer.

## Architecture sketch

Each input symbol $x$ in the algebraic layer is associated with:
- An **arithmetic variable** $v_x$ in the polynomial ring
  (already present).
- An optional set of **bit variables** $b_{x,0}, \ldots, b_{x,d-1}$
  (new), introduced lazily on demand.

When the SAT layer learns a fact about a specific bit (e.g.\ via
unit propagation: "$\mathrm{bit}_3(x) = 1$"), the algebraic layer
materialises $b_{x,*}$ if not already present, adds the
sum-decomposition equation and the idempotency equations to the
basis, and adds the unit constraint $b_{x,3} = 1$.

The reverse direction is also useful: when the algebraic layer's GB
implies a bit-level fact (e.g.\ the basis contains
$b_{x,5} - 1 = 0$), this is communicated to the SAT layer as a
unit propagation hint.

### Inferred bit variables for expressions

For derived expressions like "$\mathrm{bit}_7(3x^7 - 5y) = 0$":
introduce a fresh symbol $z := 3x^7 - 5y$ via a polynomial
equation $z - (3x^7 - 5y) = 0$, then introduce bit variables for
$z$. The GB will propagate constraints from $x$ and $y$ to $z$ via
the symbol's polynomial definition, and from $z$'s bit
decomposition to its arithmetic value.

## Concrete CBMC integration points

This is more invasive than item 7. Required changes:

1. **`poly_extractort`**: extend to handle a new `extractbit` /
   bit-access form. Currently single-bit extracts (`extract i i x`)
   are partially handled (line 279); generalise to track them as
   bit-variables in the algebraic ring.

2. **`poly_ring`**: add a notion of bit-variables vs. arithmetic
   variables (a bit on the variable record). Bit-variables get the
   idempotency equation automatically when first introduced.

3. **`boolbvt::try_algebraic_solve`**: after Buchberger, scan the
   basis for univariate-bit-linear relations and emit unit
   propagation hints.

4. **SAT-side hook**: when the SAT solver decides or propagates a
   bit literal that the algebraic layer is tracking, communicate
   this to the algebraic layer. This requires either incremental
   re-running of Buchberger (expensive) or running the algebraic
   layer at multiple SAT levels (theory-solver style). CBMC's
   current architecture runs the algebraic layer once at startup,
   not incrementally.

The fourth point is the architectural challenge: making the
algebraic layer a *real* theory solver with online interaction
requires substantial pipeline changes.

## A simpler near-term variant

A non-incremental version is more tractable:

- Eagerly introduce bit variables for all input symbols at start.
- Eagerly add idempotency and sum-decomposition equations to the
  basis.
- Eagerly add bit-level constraints from any user-visible
  `extractbit` calls in the input formula.
- Run Buchberger once.
- After Buchberger, emit equalities between SAT-level bit
  literals and bit variables that the basis has determined.

The eager variant avoids incremental theory-solver complexity but
multiplies the basis size by ~$d$ (one bit-variable per bit per
input symbol). Buchberger's cost is roughly cubic in basis size,
so we'd expect a $d^3 \approx 32^3 \sim 32{,}000\times$ slowdown
on 32-bit benchmarks. **This is almost certainly impractical**.

## What might actually work

A targeted variant: introduce bit variables only for bits that
already appear as `extractbit` operations in the input formula.
For most benchmarks this is 0 bits. For benchmarks with a few
explicit bit-level constraints (e.g.\ checking the sign bit, the
high-low bit decomposition for rounding), this is $O(1)$ bit
variables and the overhead is manageable.

The empirical question: are there CBMC benchmarks where mixed
bit-level and arithmetic reasoning would benefit from polynomial
encoding of the bit-level part? The current evaluation suite
suggests yes for a few cases (`mul_ineq_*`, `add_overflow_*`)
where the no-overflow assumption is encoded as a bit-extract
equation.

## Connection to existing extractor code

`src/solvers/algebraic/poly_extract.cpp` line 279 already handles
single-bit extracts:
```cpp
// extractbits with hi == lo: single bit, polynomial = (x >> lo) & 1
// We model this as a fresh variable b with the constraint
//   x = ... + 2^lo * b + ...  (the constraint is added via SSA equality)
```
(approximate quote). This is a starting point. Extending to handle
the idempotency constraints automatically and tracking the bit
relationship to the parent variable is the natural extension.

## Empirical hypothesis

Bit-level polynomial encoding will help on:
- Benchmarks that mix multiplication and bit-level masking (high-bit
  / low-bit access patterns).
- Cryptographic primitives that use bit-rotation in conjunction with
  multiplication.
- DSP queries where bit-truncation is a key operation.

It will **not** help on:
- Pure polynomial-identity benchmarks (already handled).
- Pure bit-vector benchmarks with no multiplication (bit-blasting
  is sufficient).

## Implementation effort estimate

- 2-3 weeks: implement the targeted variant (introduce bit vars
  only for explicit `extractbit` calls), integrate with
  poly_extract and the algebraic layer.
- 2 months: full incremental theory-solver integration with
  bidirectional communication between SAT and algebraic layers.

## Deferred

This is firmly future-paper material. The Paper 2 scope ends with
items 1-6.

## Summary

Items 7 and 8 together would turn the algebraic layer into a true
theory solver in the SMT(LRA/UF/...)-tradition, exchanging
arbitrary polynomial information with bit-blasting. This is a
natural follow-up paper. Paper 2 establishes the algebraic layer
as a useful preprocessor; the follow-up would establish it as a
peer of the bit-blast layer in the search.
