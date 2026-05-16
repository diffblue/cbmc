# Paper 1: investigation of pair_detect refinement-loop slowdown

## Symptom

In `martin-subpoly-results.md`, three benchmarks where pure
bit-blasting solves in <1 s but `--refine-arithmetic` (Paper 1's
pair-detection mode) times out at 10 s:

- `bitwidth-8-degree-5-seed-23-addition-original-native-encoding`
- `bitwidth-8-degree-8-seed-23-addition-original-native-encoding`
- `bitwidth-8-degree-12-seed-23-addition-original-native-encoding`

These are small 8-bit polynomial-identity benchmarks of the form
$p(x) + q(x) \stackrel{?}{=} (p+q)(x)$ for random polynomials $p, q$
of degrees 5, 8, 12.

## Diagnosis

Verbose-mode trace shows pair detection finds **nothing** on these
benchmarks (zero `BV-Refinement: detected ... pairs` log lines).

The benchmarks consist of a single disequality with many distinct
multiplications, each using a different power of $x$ (e.g.\
$x^2, x^3, \ldots, x^{12}$). The pair-detection algorithm in
`detect_algebraic_pairs` (`refine_arithmetic.cpp:921`) compares
flat multiset representations of factors; each multiplication has a
distinct multiset (different power of $x$), so no pairs match.

The slowdown is therefore **not** caused by pair detection itself,
but by the refinement-loop infrastructure that `--refine-arithmetic`
brings in. Each `bvmul` becomes an over/under-approximated
expression rather than a directly bit-blasted operation. The
refinement loop iterates, increasing the under-approximation bound
each time, until the proof passes. For a degree-12 polynomial in
8-bit, this can take many iterations even when the formula is
trivially UNSAT.

## Architectural tension

`--refine-arithmetic` does two distinct things:

1. **Pair detection** (Paper 1's contribution): identifies
   commutatively/associatively/distributively equivalent
   multiplications and asserts result equality at the bit level.
2. **Multiplication refinement** (legacy CBMC infrastructure):
   over-approximates `bvmul` and refines on demand.

When pair detection finds something useful (1), the refinement loop
(2) is justified — even with refinement overhead, the pair-equality
shortcut typically pays back. When pair detection finds nothing,
the refinement-loop overhead is pure cost.

## Root cause

`bv_refinementt::dec_solve` calls `detect_algebraic_pairs()`
unconditionally at the start, then enters the refinement loop
unconditionally after. There is no path that says "pair detection
found nothing; skip the refinement loop and use direct bit-blasting
instead."

```cpp
// bv_refinement_loop.cpp:37
detect_algebraic_pairs();   // may find nothing
log.debug() << "Solving with " << prop.solver_text() << messaget::eom;
unsigned iteration=0;
while(true) { ... }         // refinement loop runs regardless
```

## Recommended fix (for future Paper 1 work)

**Option A (architectural)**: Track whether pair detection found
anything. If not, skip the refinement loop and fall through to
direct bit-blasting on the constructed formula.

```cpp
size_t pairs_emitted = detect_algebraic_pairs();  // returns count
if(pairs_emitted == 0)
{
  // No pair detection benefit; bypass refinement loop.
  return prop_solve_direct();  // standard SAT call
}
// Standard refinement loop.
while(true) { ... }
```

**Option B (separate flags)**: Split `--refine-arithmetic` into
`--detect-pairs` (pair detection only, no refinement loop) and
`--refine-mul` (refinement loop only). User opts in to either or
both.

**Option C (status quo + documentation)**: Document that
`--refine-arithmetic` adds refinement overhead, so it should only
be used on benchmarks where pair detection is expected to fire.
Effectively a heuristic guidance for users.

Option A is the cleanest. Option B is more flexible but doubles
the flag surface. Option C is zero-effort but deflects the issue
to users.

## Effort estimate for Option A

- Add `pairs_emitted` return value to `detect_algebraic_pairs()`:
  trivial.
- Bypass the refinement loop when 0 pairs: needs to check whether
  the rest of the bv_refinementt setup (over/under approximations
  for each `bvmul`) is also bypassable. If not, the refinement
  loop's first iteration must still run, but it can return as soon
  as it finds either SAT (no refinement needed) or UNSAT with no
  proof failures.
- Estimated 2-4 hours implementation, plus benchmark validation.

## Empirical impact (estimated)

The 3 Martin-benchmark regressions are the visible symptom. The
broader impact: `--refine-arithmetic` is currently a power-tool
that helps on benchmarks with pair-detection opportunities but
hurts on benchmarks without them. Fixing this with Option A would
make `--refine-arithmetic` a strict superset of pure bit-blasting.

## Status (2026-05-16)

Diagnosed but not fixed. Documented as a Paper 1 issue separate
from the Paper 2 work. Out of scope for the current Paper 2
hardening session.

## Reproduce

```bash
# Reproduce the slowdown:
test=/tmp/martin-bench/seed-23/bitwidth-8-degree-5-seed-23-addition-original-native-encoding.smt2
ulimit -v 57591731

# Direct bit-blasting (~0.1 s):
time timeout 5 env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 \
  build/bin/smt2_solver --cadical "$test" \
  --multiplier-encoding shift-add

# pair_detect (T/Os):
time timeout 15 env DISABLE_SIMPLIFY=1 DISABLE_ALGEBRAIC=1 \
  build/bin/smt2_solver --cadical "$test" \
  --refine-arithmetic --multiplier-encoding comba-cs
```

The output of the second includes "BV-Refinement: iteration 4"
when the timeout hits — confirming the slowdown is the refinement
loop, not pair detection.
