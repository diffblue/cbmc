# Plan: Faster Multiplication, bvudiv/bvurem Polynomial Encoding,
# and Faithful Toom-Cook 4-way SABER Verification

Status: 2026-05-29. Owner: Kiro / Markus.

## Three open questions, three answers

### Q1. Bring bvudiv/bvurem into the polynomial fragment

**Yes, this is possible.** Standard technique: introduce fresh
quotient/remainder variables and use the definitional equation
as a polynomial constraint, with the range constraint provided
by the existing Re 4 universal-relational machinery.

For each `bvudiv s t` and `bvurem s t`, introduce fresh `q, r`
and add:

```
q * t + r - s = 0                 (polynomial in ZMod(2^d), no overflow)
t = 0  =>  r = s  AND  q = ~0     (SMT-LIB special case)
t != 0 =>  r < t                  (range, via bvult / Re 4 sub-goal 6)
```

Then `bvurem s t = r` and `bvudiv s t = q` in the polynomial system.
Buchberger gets the polynomial equation; the bit-decomposition
layer gets the range predicate. Together they uniquely determine
`q, r` (no overflow because at integer level
`q.val * t.val + r.val = s.val < 2^d`).

**Soundness sketch.** The integer-level identity
`s.val = (s.val / t.val) * t.val + (s.val mod t.val)` plus
`0 <= s.val mod t.val < t.val < 2^d` and
`s.val / t.val * t.val < s.val < 2^d` means there is no overflow
when reducing the integer equation modulo `2^d`. Hence the
polynomial equation `q * t + r - s = 0` in ZMod(2^d) is true
for the canonical representatives. The range constraint
`r < t` (when t != 0) restricts the choice of `(q, r)` to the
unique pair satisfying integer division. (Without the range
constraint, the polynomial equation alone has many solutions:
e.g. `q = 0, r = s` always satisfies `0*t + s = s mod 2^d`.)

**Anticipated impact.**

- bw512_1: `(bvadd (bvnot s) (bvurem s t)) != (bvnot (bvmul t (bvudiv s t)))`
  encodes to `t * q + r - s != 0`, which contradicts our added
  constraint `t * q + r - s = 0`. Buchberger refutes in one
  reduction step.
- bw512_12: similar structural reasoning, more complex case
  analysis on s = 0 vs s != 0.
- bw512_14: relational, depends on Re 4 sub-goal 6 finishing.

**Effort**: 1-2 weeks (engineering + Lean formalisation).

**Implementation sketch.**

`src/solvers/algebraic/poly_extract.cpp::to_polynomial` gains a
case for `bvudiv` / `bvurem` that:
1. Recursively encodes `s` and `t` into polynomials.
2. Introduces fresh symbol-table entries `q_<id>` and `r_<id>`.
3. Adds the side equation `q*t + r - s` to `equations`.
4. Adds the predicate `bvult r t` (for the t != 0 case) to
   `algebraic_predicates`.
5. Adds the t = 0 case as conditional equations or
   `(t = 0) => r = s` and `(t = 0) => q = -1` predicates.
6. Returns `q` (for bvudiv) or `r` (for bvurem) as the polynomial.

The conditional-equation case needs careful handling. Two
options:
- **Option A**: emit two separate equations guarded by t = 0
  status, and let Buchberger reason about both branches.
- **Option B**: introduce auxiliary variables that absorb the
  conditional, e.g. `q_safe = q + (t = 0 ? bridge : 0)`.

Option A is cleaner; Option B might integrate better with the
existing strong-Gröbner-basis computation.

**Lean side.** New module `BvDivPolyEncoding.lean` proving:
- `bvudiv_polynomial_correctness`: for any s, t in ZMod(2^d) and
  q = bvudiv s t, r = bvurem s t, the polynomial relation
  `q * t + r = s` holds in ZMod(2^d).
- `bvudiv_range_correctness`: the range predicate `r < t`
  holds when t != 0.
- `bvudiv_unique_solution`: given the equation + range, the
  pair (q, r) is uniquely determined.

### Q2. Faithful Toom-Cook 4-way SABER without specialised structure recognition

The current paper text mentions two alternatives in passing for
this open challenge; "specialised Toom-Cook structure
recognition" is one, and "decomposition into evaluation,
multiplication, and interpolation sub-lemmas" is the other.

The **lemma-based decomposition** is general — it's just CBMC's
standard `assert ⊕ assume` decomposition technique applied to
a structured proof obligation. No solver-side magic, no
Toom-Cook-specific code in our procedure. The user prefers this.

**Specific decomposition for Toom-Cook 4-way**:
1. Evaluation lemma: at each of the 7 evaluation points
   `{0, 1, -1, 2, -2, 3, infinity}`, assert that
   `f_eval[i] = sum(f[j] * point[i]^j)`.
2. Pointwise multiplication lemma: at each evaluation point,
   `h_eval[i] = f_eval[i] * g_eval[i]`.
3. Interpolation lemma: `h[k] = sum(L_k(point[i]) * h_eval[i])`
   where `L_k` are the Lagrange basis polynomials (involves
   division by 3, 9, 15 — all odd, hence units in ZMod(2^d)).
4. Schoolbook equivalence: schoolbook coefficients equal
   Toom-Cook coefficients.

Each sub-lemma is a *small* polynomial identity. The composition
gives the full equivalence. This is a research-engineering
effort (~2-4 weeks) but **non-specialised**: each sub-lemma is
solved by our existing Buchberger + Re 4 procedure, no extra
machinery in the solver itself.

Other non-specialised paths (for additional speedup):

- Faster polynomial multiplication (Q3 below).
- Better S-poly heuristics in Buchberger (general, applicable
  to all queries).
- Lazy bit-blasting of subexpressions (helps when algebraic
  refutes before SAT phase).

### Q3. Karatsuba / Toom-Cook for polynomial multiplication

**Yes, both work over ZMod(2^d).**

| Algorithm | Asymptotic | Coefficient ring requirement |
|---|---|---|
| Schoolbook | O(N^2) | +, -, * |
| Karatsuba | O(N^1.585) | +, -, * |
| Toom-Cook 3-way | O(N^1.46) | +, -, *, /3, /9 (units in ZMod(2^d)) |
| Toom-Cook 4-way | O(N^1.40) | +, -, *, /3, /9, /15 (units in ZMod(2^d)) |
| FFT | O(N log N) | requires high-order roots of unity |

For our use case (polynomial multiplication in Buchberger,
SABER N up to ~1024):

- **Karatsuba** is the easy win. Only requires +, -, * in the
  coefficient ring. Straightforward to implement and formalise.
- **Toom-Cook** also works (3, 9, 15 are odd, hence units in
  ZMod(2^d)). More complex (evaluation + pointwise mult +
  interpolation). Stronger asymptotics, larger constants.
- **FFT** is a poor fit. ZMod(2^d) lacks high-order roots of
  unity (the multiplicative group of units has structure
  Z/2 x Z/2^{d-2}, which doesn't give us the 2^k roots needed
  for size-2^k FFTs).

**Implementation challenge**: our `polynomialt` is *multivariate*.
To apply Karatsuba/Toom-Cook, group terms by their degree in a
chosen "main variable" (the SABER polynomial variable x in
practice), reducing to univariate polynomial multiplication
where the algorithms apply directly.

**Phase 1 (Karatsuba) detailed plan**:
1. Add `polynomialt::karatsuba_multiply` as a peer to the
   existing schoolbook multiplication.
2. Decision logic in `operator*`: pick a main variable
   (heuristic: the variable with the largest degree spread),
   group both polynomials by main-variable degree, and recurse.
   Below a threshold (e.g. N=16), fall back to schoolbook.
3. Output Karatsuba-style splits: `f = f_lo + x^m * f_hi`,
   `g = g_lo + x^m * g_hi`,
   `f * g = f_lo * g_lo + x^{2m} * f_hi * f_hi
            + x^m * (f_lo * g_hi + f_hi * g_lo)`,
   computed via three sub-multiplications:
   `P0 = f_lo * g_lo`, `P2 = f_hi * g_hi`,
   `P1 = (f_lo + f_hi) * (g_lo + g_hi) - P0 - P2`.
4. Lean theorem: `karatsuba_correct` proves
   `karatsuba_multiply f g = f * g` as multivariate polynomials.

**Phase 1 expected speedup on SABER**:
- N=64: minimal (close to threshold).
- N=256: ~2x.
- N=768: ~3-5x (closer to asymptotic).
- N=1024: ~5x.

**Phase 1 vs Toom-Cook**: start with Karatsuba (simpler),
upgrade to Toom-Cook if Karatsuba isn't enough for the SABER
target. Toom-Cook 4-way's O(N^1.40) gives another ~2x at
N=1024 over Karatsuba.

## Three-phase work order

### Phase 1: Polynomial Karatsuba (this commit chain)
- `polynomialt::karatsuba_multiply` with schoolbook fallback below threshold.
- Lean theorem in `Karatsuba.lean` (new module).
- Benchmark on SABER N=64, 256, 768, and on the high-bitwidth
  (a+b)^d sample to verify no regression on small cases.

### Phase 2: bvudiv/bvurem in the polynomial fragment
- Extend `to_polynomial` with q, r aux variables.
- Add range constraint via Re 4 predicate path.
- Special-case the t = 0 branch.
- New Lean module `BvDivPolyEncoding.lean`.
- Test on bw512_1 (expected unlock), bw512_12, bw512_14.

### Phase 3: SABER Toom-Cook 4-way via lemma decomposition
- assert-then-assume on the four sub-lemmas
  (evaluation, pointwise, interpolation, schoolbook
  equivalence).
- Verify each sub-lemma at N = 4, 8, 16.
- Update the paper either way.

## Risks and mitigations

- **Phase 1 regression risk**: Karatsuba has overhead per call;
  small polynomials get slower. Mitigation: threshold-based
  fallback to schoolbook below N = 16.
- **Phase 2 conditional-encoding subtlety**: the t = 0 case
  may interact badly with strong Gröbner basis computation.
  Mitigation: prototype on a small benchmark before scaling up.
- **Phase 3 sub-lemma blow-up**: Lagrange basis coefficients
  for Toom-Cook 4-way have large rational coefficients (think
  6, 24, 120 in the denominators) that need careful handling
  in ZMod(2^d). Mitigation: precompute the coefficients in
  ZMod(2^d) as constants in the assert; the verification then
  doesn't need to compute the divisions.

## Note on Toom-Cook as a Phase 1 option

Toom-Cook 3-way or 4-way could replace Karatsuba in Phase 1
if Karatsuba's speedup proves insufficient for the SABER target.
The implementation cost is ~2x that of Karatsuba (more bookkeeping
for evaluation/interpolation), but the asymptotic improvement
matters at large N.

If Phase 1 + Karatsuba unlocks SABER at, say, N=2048, we stop
there. If it doesn't, we promote to Toom-Cook 4-way.

## Phase 1 outcome (2026-05-29): NEGATIVE for SABER

Implemented `polynomialt::karatsuba_multiply` with the standard
3-multiplication identity, threshold-tuned to 96 terms, and
mechanised in `formal-proofs/Karatsuba.lean::karatsuba_identity`
(commutative-ring proof by `ring`). The implementation is
correct (microbench shows ~2x speedup at 1024-term dense
univariate polynomials, parity at 128, and matches schoolbook
on all inputs).

**However, Karatsuba does not help any current benchmark**,
including SABER N=256 (still 11.4s) and bw=512 family (no
change). Empirical reason discovered via `ALGEBRAIC_MULT_TRACE`
instrumentation:

- SABER N=256: 82,558 polynomial multiplications, ALL with at
  most 10 terms each. Total term-pairs: 82,940. Each `a_i * b_j`
  in SABER is a single-coefficient × single-coefficient product,
  not a polynomial × polynomial product.
- bw=512 family: only 2 multiplications above threshold, both
  of shape 1 × 512 (scalar × polynomial). Karatsuba does not
  help scalar × polynomial: that's just element-wise scaling.
- All other SMT-COMP samples surveyed: max multiplication size
  is single digits.

In other words, **the bottleneck for SABER large-N is not
polynomial multiplication.** The 11s for N=256 comes from the
quadratic blow-up in the *number* of small multiplications
(O(N^2) coefficient products), not the cost of any single
multiplication. Karatsuba reduces the cost per multiplication
when the multiplications themselves are large, which is not
the regime we operate in.

**What could actually help SABER large-N:**

1. **Lazy bit-blasting** of subexpressions (already on the
   "would-need-multi-week-architectural-work" list in the
   paper). Each of the 82k single-coefficient products
   bit-blasts to ~bw^2 SAT clauses. For SABER N=256, that's
   ~14M clauses driving SAT cost.
2. **Sparse-polynomial fusion**: merge multiple `a_i * b_j`
   products that share an output coefficient into a single
   multi-variate polynomial expression that the algebraic
   solver handles directly, rather than O(N) individual
   multiplications per output coefficient.
3. **Better strong Gröbner-basis heuristics**: reduce the
   number of S-poly candidates Buchberger considers.

Karatsuba is correctly mechanised and committed regardless,
because it is a correct, formally-justified improvement that
will help the *moment* we hit a workload with large polynomial-
on-polynomial multiplications. Phase 2 (bvudiv/bvurem in the
polynomial fragment) may produce such workloads, in which case
Karatsuba is ready.

**Conclusion**: Phase 1 delivers a correct-and-formalised
Karatsuba multiplication, but the SABER >N=768 motivation does
not actually exercise the path. Move on to Phase 2 (more
impactful) and revisit polynomial-multiplication speed-ups
only if Phase 2 introduces large polynomial × polynomial
products that benefit.

### Toom-Cook decision (deferred)

Given that Karatsuba does not help any current benchmark, the
extra implementation cost of Toom-Cook 3-way or 4-way would not
pay off at the current bottleneck. We defer Toom-Cook unless
and until a workload with large polynomial × polynomial
multiplications emerges (potentially from Phase 2).
