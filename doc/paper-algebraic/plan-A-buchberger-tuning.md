# Plan A — Buchberger tuning + boolean tree walk

**Status**: detailed proposal, informed by empirical investigation
documented in this file.

## Empirical motivation

I instrumented `strong_groebner_basist::compute()` and ran the
cohencu polynomial identity at varying bitwidths:

```
eq A:  z + y - 7 - 3n² - 9n = 0         (in ZMod 2^d)
eq B:  y - 3n - 3n² - 1 = 0
diseq: z != 6 + 6n   [Rabinowitsch: e * (z - 6 - 6n) - 1 = 0]
```

Conclusion (immediate, by polynomial elimination):
`A - B → z - 6 - 6n`, then S-poly with Rabinowitsch's polynomial
gives the constant `-1 ≡ 2^d − 1` (odd) — UNSAT.

Empirical results with the **current LIFO pair selection**:

| Bitwidth | Result | Steps | Basis size at termination |
|----------|--------|-------|--------------------------|
| bw = 4   | UNSAT  | 2923  | 38                       |
| bw = 8   | UNKNOWN (step limit hit, falls through to SAT) | 91 875 | 90+ |
| bw = 16  | UNKNOWN | hits step limit | 110+ |
| bw = 32  | UNKNOWN | hits step limit | 100+ |

The trace at bw=8 shows the basis growing through repeated S-poly
reductions that produce **even constants only** (8, 128, 192, 32,
144, 216, …). Even constants are non-units in ZMod(2^d) and do NOT
trigger UNSAT (cf. `formal-proofs/GroebnerSoundness.lean::ZMod.two_not_isUnit`).
The critical S-polynomial S-poly(A, B) = `z - 6 - 6n` is processed
LAST under LIFO, by which time the basis has grown so large that
the algorithm hits the step limit before reaching the pair.

I then changed the pair-selection strategy to **min-LCM-degree
("normal selection" / "sugar")** — the textbook Buchberger
heuristic:

| Bitwidth | Result | Steps | Basis size at termination |
|----------|--------|-------|--------------------------|
| bw = 4   | UNSAT  | 9     | 6                        |
| bw = 8   | UNSAT  | 9     | 6                        |
| bw = 16  | UNSAT  | ≤ 12  | ≤ 8                      |
| bw = 32  | UNSAT  | ≤ 12  | ≤ 8                      |

The normal selection picks S-poly(A, B) FIRST because `lcm(LM(A),
LM(B)) = n²` (degree 2) is smaller than other pair LCMs. The
S-poly reduces to `z - 6 - 6n`. Combined with Rabinowitsch's
polynomial, we get `e * (z - 6 - 6n) - 1` and after one more
reduction `-1` (odd), triggering UNSAT.

**No regressions** observed on:
- bw=512 family (1, 7, 12, 14, 15) — same timings
- wienand commute*/distrib* — same timings (~6ms)
- SABER (n=32, 128, 256) — same timings
- Full SMT-COMP sample (66 benchmarks) — same 36/66

## Plan A scope

Plan A combines **two complementary changes** that are needed
together to unlock real-world (not synthetic) cohencu-style
benchmarks:

### A.1 — Buchberger pair-selection strategy (~50 lines, ~1 day)

**Change**: replace the LIFO `pairs.back() / pairs.pop_back()`
selection in `strong_groebner_basist::compute()` (groebner.cpp,
~line 374) with a **min-LCM-degree** selection that picks the pair
whose `lcm(LM(polys[i]), LM(polys[j]))` has the smallest total
degree. Ties broken by FIFO order.

**Soundness**: pair-selection strategy doesn't affect the
correctness of Buchberger's algorithm; only termination speed and
the size of the intermediate basis. The existing soundness chain
(`buchberger_unsat'`, `s_poly_in_ideal`, `reduce_in_ideal`,
`scale_in_ideal`, `two_trick_preserves_ideal`) is unchanged. The
termination criterion (`pairs_since_last_progress >
pairs_at_last_progress`) is also unchanged.

**Risk**: low. Per-pair selection adds O(|pairs|) work per step,
but |pairs| is small at the steps that matter (when the basis is
~10 elements). Empirically no observed slowdown.

**Implementation**:
```cpp
// In compute(), replace:
//    auto [i, j] = pairs.back();
//    pairs.pop_back();
// with:
auto best_idx = select_pair(pairs, polys);
auto [i, j] = pairs[best_idx];
pairs[best_idx] = pairs.back();
pairs.pop_back();

// where select_pair() returns the index of the pair with
// minimum lcm-degree:
static std::size_t select_pair(
  const std::vector<std::pair<std::size_t, std::size_t>> &pairs,
  const std::vector<polynomialt> &polys);
```

Implementation details:
- LCM degree computed by merging the leading-monomial variable
  lists with `max` on shared variables (already implemented in
  `s_polynomial`).
- For pairs where one polynomial is zero or out of bounds, treat
  LCM degree as `~0u` (lowest priority).
- Add an env var `GB_LIFO=1` to fall back to LIFO for ablation
  experiments. Default behavior changes to normal selection.

**Lean impact**: minimal. Add a new theorem:
```
theorem normal_selection_sound :
  buchberger_step (with normal_selection) preserves ideal membership
```
The proof reuses existing soundness lemmas; pair-selection
strategy is orthogonal to soundness.

**Test plan**:
- Add unit test for `cohencu_simple` at bw=4/8/16/32. Expect
  UNSAT in <100 steps each.
- Run full SMT-COMP sample. Expect 0 regressions, possibly some
  unlocks (geo3.c_5 if combined with walk).
- Run unit tests `[groebner]` to ensure existing Lean-traced
  invariants hold.
- Run regression suite (`regression/smt2_solver`) to ensure no
  test break.

**Estimated effort**: 1 day (implementation + tests + Lean
update).

### A.2 — Boolean tree walk + ITE-rebuild (~200 lines, ~3 days)

**Change**: extend `boolbvt::set_to()` (boolbv.cpp) to walk the
boolean tree of top-level assertions, surfacing equalities buried
in AND/OR/NOT/let nodes for `algebraic_equalities` collection.
Also recognise the post-Phase-2.5 shape `(if c (= sym A) (= sym
B))` and rebuild as `(= sym (if c A B))`.

**This was attempted in Phase 2.7** with bounded gates (leaves≤200,
depth≤100, body-size≤500, total-add≤50). It preserved baseline
(0 regressions) but produced 0 unlocks ALONE. Combined with A.1
(Buchberger normal selection), it unlocks geo3.c_5 immediately
and is needed to unlock cohencu_0/1/2/3.

**The Phase 2.7 attempt also caused 5 regressions** under specific
conditions (sage_app1, sage_app7, Sage2_bench_15251/17485,
umulov2bw0512). The regressions are due to walk-collected
equalities flooding the algebraic worklist when the formula is
NOT polynomial-friendly (heavy bvshl/bvor structure with no
arithmetic content). The bvmul-presence gate (only collect leaf
equalities containing `ID_mult` somewhere) eliminated those
regressions but also blocked the cohencu IF-rebuild equality
`sym = (if c 1 0)` (which has no bvmul).

**The right gate** combining both insights:
1. ALWAYS collect IF-rebuild equalities (`(if c (= sym A) (= sym B))`
   → `(= sym (if c A B))`), regardless of bvmul presence. These
   come from Phase 2.5 push-through-ite and are SSA definitions.
2. For OTHER leaves (direct equalities/disequalities under AND/OR/NOT/
   let), require bvmul presence in operands.
3. Maintain the size guards (leaves≤50, depth≤100, body-size≤500
   for let inlining, total-add≤30) to avoid pathological costs.
4. Add per-call total-eq-volume cap: if cumulative
   `algebraic_equalities.size()` exceeds say 200 across all
   set_to calls, stop adding.

**Lean impact**: new module `formal-proofs/AlgebraicTreeWalk.lean`
with theorems:
```
theorem walk_collects_implied_equality :
  ∀ (e : Expression) (v : Bool),
    set_to(e, v) ⊨ collect(e, v)
  // Each leaf collected by walk is implied by the parent assertion

theorem if_rebuild_equivalence :
  (if c (= sym A) (= sym B)) ↔ (sym = (if c A B))
  // Soundness of the if-rebuild step
```

**Risk**: moderate. The walk has known regression patterns
(sage_app1 et al). Need careful gating + ablation testing.

**Test plan**:
- Test on cohencu_0/1/2/3 (expect: UNSAT in <30s each with A.1+A.2)
- Test on geo3.c_5 (expect: UNSAT, already shown)
- Test on Sage2_bench_15251, sage_app1_bench_292 (expect: NO
  regression, baseline behavior preserved by gating)
- Run full SMT-COMP sample (expect: +5 to +8 unlocks)

**Estimated effort**: 3 days. Most of the time is on the gating
heuristics — getting them right requires iterative ablation.

### A.3 — Optional: F4 / matrix-style reduction (~2-3 weeks, deferred)

The current Buchberger uses incremental reduction (one S-poly at a
time, reduce by basis). **F4** (Faugère 1999) collects multiple
S-polynomials and reduces them via a single matrix row reduction.
For polynomial systems with many similar leading monomials (like
the cohencu basis growth at bw=8 — 90+ basis elements with leading
n²), this can be orders of magnitude faster.

**Defer this** — it's a significant rewrite (the polynomial
representation might need adjustment, the matrix kernel needs
implementation). Plan A.1 + A.2 is sufficient to address the
cohencu and similar polynomial-fragment benchmarks. F4 would be a
Phase 3 item if we want to push polynomial reasoning further.

## Plan A — total scope and risk

| Item | Lines | Effort | Risk | Expected unlock |
|------|-------|--------|------|-----------------|
| A.1 — Pair selection | ~50 | 1d | Low | Foundation; unlocks alone: 0 |
| A.2 — Tree walk | ~200 | 3d | Medium | +5 to +8 (cohencu* 4, geo3, possibly Sage2_bench_9381, Favaro, VS3_*) |
| A.3 — F4 reduction | ~1500 | 2-3w | High | DEFERRED |

**Plan A total**: ~1 week of implementation + ~3 days of testing
and Lean formalisation. Total ~2 weeks. Expected **+5 to +8**
SMT-COMP unlocks (currently solving 36/66; would reach 41-44/66).

## Plan A — Lean formalisation

New theorems:

1. `formal-proofs/StrongGB.lean`:
   ```
   theorem normal_selection_preserves_ideal_invariant :
     ∀ (basis : List Polynomial) (pair_strategy : PairStrategy),
       sound_ideal_invariant (run_buchberger basis pair_strategy)
   // Pair selection is orthogonal to soundness.
   ```

2. `formal-proofs/AlgebraicTreeWalk.lean` (new):
   ```
   theorem leaf_eq_implied_by_andtree (e : Expr) (val : Bool) :
     ∀ leaf ∈ collect_walk(e, val),
       e = val ⊨ leaf

   theorem if_rebuild_equivalence (c : Expr) (sym A B : Expr) :
     (if c then (sym = A) else (sym = B)) ↔ (sym = if c A B)
   ```

Both proofs are direct case analyses — small (~50 lines each).

## Plan A — paper impact

If Plan A unlocks +5-8 SMT-COMP benchmarks, the paper updates:
- §empirical: from 36/66 to 41-44/66 (~14% improvement on the
  stratified sample).
- §technique: new subsection on "Pair-selection strategy in
  ZMod-Buchberger". Discuss the LIFO → normal selection finding,
  the empirical impact (cohencu refutation step count), and the
  formal soundness story.
- §future-work: F4 reduction for polynomial-fragment benchmarks
  with deeper reduction sequences.

The pair-selection finding is a **research-paper-worthy result**
on its own: "for ZMod-Buchberger over bit-vector polynomial
systems, the LIFO pair selection (commonly used in implementations
because it requires no ordering) is up to 10000× slower than
normal selection on cohencu-style invariants. Normal selection
incurs O(|pairs|) per pair but is empirically free at the steps
that matter."

## Plan A — risks and mitigations

1. **The combined walk + GB might introduce subtle regressions
   we haven't seen**. Mitigation: extensive ablation, per-benchmark
   timing comparison, opt-out env vars.
2. **Cohencu_0 might still T/O even with full Plan A**. Mitigation:
   if cohencu_0 doesn't unlock with Plan A, the gap is
   ITE-handling of polynomial conditions, which would need a
   small extension to Tseitin propagation (not in scope here).
3. **The walk might still mis-collect on benchmarks not in our
   sample**. Mitigation: keep all gates (size, depth, leaf cap)
   conservative. Default behavior should be near-no-op for
   non-polynomial-friendly formulas.

## Plan A — out of scope for this iteration

- F4 reduction (A.3, deferred)
- ITE-handling of polynomial conditions (e.g., `sym = ite(z = X, A,
  B)` where the condition `z = X` is polynomial)
- Multi-variate Frobenius (current implementation handles
  single-variable bit clamping; extending to multi-bit is non-trivial)
- Variable ordering optimisation (we use grevlex globally; some
  benchmarks might benefit from per-formula variable ordering
  tuning)
