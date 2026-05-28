# Implementation findings from the formal proof work

This document records implementation-level findings that surfaced during
the formal-proof effort but were not previously called out as part of
the proof contributions themselves.

## Potential bug: progress tracking misses 2-trick additions

**Location**: `src/solvers/algebraic/groebner.cpp::compute`, the main
Buchberger loop (around lines 309–355).

**Severity**: completeness bug, NOT soundness. The algorithm can return
`UNKNOWN` when more processing would have produced `UNSAT`. Existing
returned `UNSAT` results remain correct.

**Description**: The loop tracks progress with two variables:
```cpp
std::size_t pairs_since_last_progress = 0;
std::size_t pairs_at_last_progress = pairs.size();
```
Each iteration:
1. Pops a pair, increments `pairs_since_last_progress`
2. Computes S-polynomial. If it reduces to a non-zero `r`, adds `r` to
   `polys`, adds new pairs `(k, new_idx)` for `k < new_idx`, and resets
   the counters: `pairs_since_last_progress = 0; pairs_at_last_progress
   = pairs.size();`
3. Runs the 2-trick over all of `polys`. Can add multiple new elements
   and pairs. **No counter reset.**

The exit condition `pairs_since_last_progress > pairs_at_last_progress`
triggers prematurely in two scenarios:
- **B1**: S-poly fails (no reset) but 2-trick adds elements. The new
  pairs are pushed but `pairs_at_last_progress` stays stale.
- **B2**: S-poly succeeds (reset happens) and then 2-trick adds more
  elements. The reset captured `pairs.size()` BEFORE the 2-trick's
  additions, so those additions are not counted.

**Trace through example**: starting with 3 polynomials and 3 pairs
`[(0,1), (0,2), (1,2)]`, where `polys[2]` has non-unit leading
coefficient:
1. Pop `(1,2)`, S-poly empty, counter=1.
2. 2-trick adds `polys[3] = polys[2] * 2^k`, with new pairs
   `(0,3), (1,3), (2,3)`. Stack now: `[(0,1), (0,2), (0,3), (1,3), (2,3)]`.
3. Pop `(2,3)`, counter=2. Pop `(1,3)`, counter=3. Pop `(0,3)`, counter=4.
4. Check `4 > 3` → exit. **Pairs `(0,1)` and `(0,2)` never processed.**

If `S-poly(polys[0], polys[1])` would have reduced to a unit constant,
we incorrectly return `UNKNOWN` instead of `UNSAT`.

**Suggested fix**: at the end of each iteration, reset progress tracking
if any new element was added (by either S-poly or 2-trick):
```cpp
size_t old_polys_size = ... // capture at iteration start
// ... S-poly and 2-trick processing ...
if(polys.size() > old_polys_size)
{
    pairs_since_last_progress = 0;
    pairs_at_last_progress = pairs.size();
}
else
{
    ++pairs_since_last_progress;
}
```

**How the proofs surfaced this**: while preparing direct PROOF: refs for
`s_polynomial`, `strong_reduce`, `reduce_by_basis` against
`BuchbergerCorrectness.lean`, I traced through how the abstract
`buchberger_terminates` and `stable_implies_no_new` connect to the
concrete loop's exit condition. The abstract proof assumes "every pair
in the basis × basis has been processed at termination" but the
concrete code can exit before that holds when 2-trick injects
unprocessed pairs.

## Optimization opportunities

### Memoize `smarandache_function` per d

**Location**: `src/solvers/algebraic/vanishing.cpp::generate_zfp_generators`.

`smarandache_function(d)` is called once per variable. For an n-variable
problem with the same `d`, it's called `n` times computing the same
result. The function loops `k = 1, 2, ...` summing `nu2(k)` until reaching
`m = d`. For typical `d ≤ 64`, this is `O(d)` time per call.

**Suggested fix**: cache the result in a `std::unordered_map<unsigned,
unsigned>` keyed by `d`. Saves `O(n*d)` total across all variables.

### Memoize `to_polynomial` for shared subexpressions

**Location**: `src/solvers/algebraic/poly_extract.cpp::to_polynomial`.

CBMC's `exprt` uses structural sharing via `irept`, so identical
subexpressions can appear multiple times in a formula. `to_polynomial`
converts them recursively without caching. For formulas with significant
sharing (e.g., DAG-shaped expression trees from common subexpression
elimination), this duplicates work.

**Suggested fix**: maintain a memoisation table keyed by `exprt` pointer
or hash, populated on first conversion. Saves potentially significant
work on large formulas.

**Caveat**: only sound for stateless conversions. `to_polynomial` mutates
`bitwidth` and `var_input_widths` as a side-effect of typecast/zero_extend
handling, so the cache key needs to include the relevant context, or the
side effects need to be made explicit.

### Consider closed-form for SF(2^d) via Legendre's formula

**Mathematical observation**: `nu2_factorial(k) = k - s_2(k)` where
`s_2(k)` is the binary digit sum (Legendre's formula). So
`SF(2^m) = min { k : k - s_2(k) ≥ m }`.

For `m` of typical size (up to 64), this gives `k ≈ m + log_2(m)`. A
closed-form lookup or a single binary search would be `O(log m)` instead
of `O(m)`.

**Practical impact**: minimal at typical `d`. Worth flagging for
documentation but not urgent.

## Confirmed correct (not a bug)

The proof work also raised questions that turned out to NOT be bugs:

### `monomialt::operator<` returns `vars.size() > other.vars.size()` at the end

This case only triggers when both iterators reach end without finding a
disagreement, which means the monomials are equal. For equal monomials,
`vars.size() == other.vars.size()`, so the return is `false` (irreflexive).
Verified correct via the formal proof of `grevlexLt_irrefl` in
`PolyRing.lean`.

### `extract_candidate` on non-unit leading coefficient

When `v_x = ν₂(c) > 0`, the equation `c·x + d = 0` has either zero or
`2^v_x` solutions. The C++ code picks one specific solution
`val % m` and adds it to the assignment.

Concern: is picking one of multiple solutions sound?

Answer: yes — `extract_candidate` is a **heuristic** for the SAT solver,
not a theorem prover. Returning *any* candidate that satisfies the
extracted polynomials is sound. Returning a wrong candidate (one that
doesn't extend to a full solution) is also fine because the SAT solver
adds it as soft assumptions and rejects it via standard learning if
inconsistent.

### `inverse_mod_2d(a, 0) = 0`

In `ZMod 1` (the trivial ring), 0 = 1, so 0·0 = 0 = 1, i.e., 0 IS the
inverse of 0. The function's special case is correct.

## How the proof work led to insights

The biggest specification-level finding (the false `two_trick_saturation_complete`)
is documented in `MATHLIB_CANDIDATES.md` and the paper.

For implementation-level insights, the proof work helped by forcing me to
trace through the exact information flow:
- Building `BuchbergerCorrectness.lean` ↔ groebner.cpp correspondence
  surfaced the progress-tracking bug.
- Building `Encoding.lean` highlighted the lack of memoisation in
  `to_polynomial`.
- Building `Vanishing.lean::nu2Factorial_eq_padicVal` (Legendre's
  formula) revealed the closed-form for `smarandache_function`.

## Recommendation

The progress-tracking bug should be fixed. The fix is small and isolated.
A regression test would be helpful, though constructing a minimal
reproducer requires careful crafting of the polynomial system.

The optimization opportunities are worth implementing if performance is
ever a concern, but they're not urgent.

## Why was this missed before, and how can we do better?

### What happened

When I first added the `// PROOF:` cross-reference to
`BuchbergerTermination.lean::stable_implies_no_new`, I checked:
1. The Lean theorem exists with that exact name. ✓
2. The theorem's content (at a glance) is about "stability ⇒ no new
   elements" which matches the C++ comment. ✓

But I did **not** trace through whether the C++ loop's notion of
"stability" matches the Lean theorem's notion. The Lean theorem says
"if for all `x ∈ R`, `Ideal.span (insert x S) = Ideal.span S`, then
the candidate set is in the ideal." The C++ approximates this by:
"if `pairs_since_last_progress > pairs_at_last_progress`, the basis
is stable." But the C++ approximation is only valid if **every pair**
has been processed at least once when the threshold is reached.

The 2-trick step pushes new pairs without resetting counters, breaking
that invariant. Pure name-matching missed it.

### Why pure name-matching is insufficient

The fundamental issue: `// PROOF: ...::theorem_name` is a
**citation**, not a **proof**. A citation says "this concept is
formalised over there"; it does not say "the C++ code correctly
implements the concept."

For most of our theorems this works fine because the C++ does the
"obvious" thing. But for non-trivial loop invariants (like the
Buchberger termination criterion), the C++ implementation is a
specific encoding of the abstract concept, and the encoding can
diverge.

### Concrete improvements

These would have caught the bug, ranked by effort:

**1. Explicit invariant statement in the PROOF: comment** (low effort).
Each cross-reference should explicitly state the invariant it assumes
and how the C++ code maintains it:
```cpp
// PROOF: formal-proofs/BuchbergerTermination.lean::stable_implies_no_new
//   ASSUMES: every pair (i,j) with i,j < |basis| has been processed.
//   MAINTAINED BY: the loop pops every pair before exit. (See progress
//   tracking via pairs_since_last_progress / pairs_at_last_progress.)
```
Writing this forces the reviewer to ask "is the invariant actually
maintained?" — which is exactly the question that catches the bug.

**2. Property-based testing of invariants** (medium effort).
For each contract-level theorem, write a test that probes its
assumed invariant directly:
```cpp
// Test: when compute() returns UNKNOWN, every pair was processed
// or skipped intentionally (i,j out of range, polys[i].is_zero()).
```
Random polynomial systems would have eventually triggered the bug as
non-determinism in input generation.

**3. Refinement-style operational semantics** (high effort).
Model the C++ loop as a Lean state machine, prove it satisfies the
abstract specification (`Ideal.span (basis at termination) = Ideal.span F`
AND `if exit-with-stable, then for-all-x, x ∈ Ideal.span basis`). This
is what we do for the `Defer.lean` semantic axioms — the same approach
applied to Buchberger would catch any divergence.

**4. Coverage-driven proof depth** (medium effort).
For each entity in `COVERAGE_AUDIT.md`, after assigning COVERED status,
ask: "is the Lean theorem about the *abstract* concept or the *concrete*
implementation?" If abstract, add a connecting lemma that bridges them
(e.g., a Lean theorem stating the C++ loop's exit condition implies
stability in the abstract sense).

### Specific to the Buchberger termination case

The simplest improvement going forward:
- Document the loop's invariant (the precondition for exit) in code:
  "INVARIANT: when `pairs_since_last_progress > pairs_at_last_progress`,
  every pair `(i, j)` with `i < j < |polys|` has been popped from
  `pairs` since the last progress event."
- Verify the invariant is maintained on every loop branch.

The 2-trick branch violates the invariant. Either the invariant must
be weakened, or the loop must restore it. The fix restores it (by
counting the 2-trick's growth as a progress event).

### Take-home lesson

Cross-referencing abstract theorems is necessary but not sufficient.
For implementations that are non-trivial encodings of abstract
algorithms, we need either:
- explicit invariant statements that the cross-reference implies, or
- a refinement-style proof showing the encoding is faithful.

We will adopt practice #1 (explicit invariants in PROOF: comments) for
any future complex loop invariants.
