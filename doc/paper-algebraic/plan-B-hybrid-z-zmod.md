# Plan B — Phase 2.8: Hybrid Z / ZMod polynomial system for overflow reasoning

**Status**: detailed proposal, informed by empirical
investigation in Phase 2.7 and the architectural review of
`poly_extract.cpp` / `poly_ring.cpp` / `groebner.cpp`.

## Empirical motivation

Phase 2.7 attempted to add `q_mul` (overflow auxiliary) for `bvmul`
within the existing single-ring extractor. The attempt failed
because the polynomial system uses a single `bitwidth` field; mixing
ZMod(2^d) and ZMod(2^{2d}) within one `poly_extractort` produces
invariant violations in `polynomialt::operator+` (precondition
`bitwidth == other.bitwidth`).

**The core issue**: in our architecture, `q_mul` MUST live in a
WIDER ring than the rest of the formula. Specifically, for a `d`-bit
multiplication `s*t`, the integer product fits in `2d` bits but
overflows `d` bits. To capture the relationship `s*t = q_mul * 2^d
+ bvmul_result` exactly, we need ZMod(2^{2d}) or larger.

In ZMod(2^d), this equation reduces to `s*t = bvmul_result`, which
is **trivially true** in our existing system (it's just the bvmul
identity) and gives no new information. Hence Phase 2.7 (Option C
as a small change in the d-bit ring) is fundamentally
incompatible with our architecture.

## Survey of benchmarks that would benefit

From the SMT-COMP sample (30 unsolved benchmarks), Plan B targets
the bit-level / circuit-equivalence cluster (~16 benchmarks):

| Family | Benchmarks | Why hybrid Z/ZMod helps |
|--------|-----------|--------------------------|
| brummayerbiere2_*ulov* (5) | overflow detection circuits | Need `q_mul = (extract 2N-1 N) (zext_N s * zext_N t)` |
| log-slicing_bv*div* (5) | bvudiv soundness via slicing | Need `q*t + r = s` at integer level |
| galois_iffyInterleavedModMult (2) | modular multiplication equivalence | Need `s*t mod m` as integer |
| 2017-BuchwaldFried (1) | Mul-base-disp + load + Mul + Mulh equivalence | Need `Mulh = high half of mul` |
| brummayerbiere3_isqrtadd (1) | integer square root + addition | Need integer-level reasoning |
| wienand-cav2008_Booth_mult (1) | Booth multiplier equivalence | Need full multiplier circuit reasoning |
| calypto_problem_16 (1) | sequential equivalence | Mixed |

Plan B would NOT directly unlock the polynomial-fragment
benchmarks (cohencu, geo3, Sage2_*) — those are addressed by Plan
A. The two plans are **complementary**.

## Plan B architecture

### B.1 — The hybrid polynomial system

We introduce **two parallel polynomial systems**:

1. **Main system** in ZMod(2^d) — `d` is the formula's primary
   bitwidth. All existing equalities, disequalities, and
   relational predicates extracted by `poly_extractort` go here.
   This is the current system unchanged.

2. **Wide system** in ZMod(2^{2d}) (or some chosen wider d') —
   contains overflow auxiliaries (`q_mul`, `r_mul`) for each
   detected `bvmul`-overflow site, plus the integer-level
   constraint `s_w * t_w = q_mul * 2^d + r_mul` (where `s_w`,
   `t_w` are zero-extended to 2d bits).

The systems share variables via **bit-decomposition equality**:
the bits of `r_mul` in the wide system equal the bits of
`bvmul(s, t)` in the main system. This is encoded by sharing the
bit-variable indices (the `decompose_bits` cache spans both
extractors).

### B.2 — Where overflow auxiliaries are introduced

Phase 2.8 introduces `q_mul` / `r_mul` aux variables when the
parser / extractor sees one of these patterns:

1. **High-half-of-product extraction** (brummayerbiere2_*ulov*):
   ```
   (extract (2d-1) d) (bvmul (zext_d s) (zext_d t))
   ```
   This expression IS `q_mul`. The extractor recognises this
   pattern and substitutes a fresh variable.

2. **Comparison of bvmul result to a constant or variable**:
   ```
   (bvule (bvmul s t) Y)
   ```
   When `s*t` overflows, this comparison depends on the canonical
   representative, not the integer value. Introduce `q_mul, r_mul`
   to constrain; the wider-ring system can reason about
   `s_w * t_w = q_mul * 2^d + r_mul` and `r_mul ≤ Y`.

3. **bvudiv with non-trivial quotient**:
   ```
   (bvudiv s t)
   ```
   Already handled by Phase 2 with `q*t + r - s = 0` in d-bit. With
   Plan B's wider ring, we get the **range** `0 ≤ r < t` algebraically,
   which the current encoding leaves to bit-blasting.

### B.3 — Concrete code changes

**File: `src/solvers/algebraic/poly_ring.h`**

Already has the `bitwidth` field per polynomial. Multi-ring
support is the existing model — just need to ensure the two systems
don't accidentally mix polynomials.

**File: `src/solvers/algebraic/poly_extract.h`**

Add `wide_extractor`:
```cpp
class poly_extractort {
public:
  // ... existing API ...

  /// The wider-ring extractor for overflow reasoning. When the
  /// main ring is ZMod(2^d), the wide ring is ZMod(2^{2d}) (or a
  /// larger choice). All bvmul-overflow auxiliaries live here.
  poly_extractort wide_extractor;

  /// Bit decomposition shared between main and wide rings.
  /// For each `bvmul` site (s, t) where overflow matters, we
  /// introduce `q_mul`, `r_mul` in the wide ring with bit-
  /// decompositions. The d low bits of `r_mul` are equal to the
  /// d bits of bvmul(s, t) in the main ring.
  std::map<std::pair<exprt, exprt>, std::pair<size_t, size_t>>
    bvmul_overflow_aux;  // (s, t) -> (q_mul_idx, r_mul_idx)

  /// Detect overflow patterns and introduce auxiliaries.
  void recognise_overflow_patterns(const exprt &assertion);

  /// Get the polynomial system for the wide ring.
  std::vector<polynomialt> get_wide_system() const;
};
```

**File: `src/solvers/flattening/boolbv.cpp`**

Modify `try_algebraic_solve()` to run a SECOND Buchberger pass on
the wide system:
```cpp
// After the main per-disequality refutation loop:
if (!main_refuted)
{
  // Run Buchberger on the wide system if it has any equations.
  if (!wide_extractor.empty()) {
    strong_groebner_basist wide_gb{100000};
    wide_gb.set_bit_vars(wide_extractor.get_bit_var_indices());
    auto wide_polys = wide_extractor.get_wide_system();
    if (wide_gb.compute(wide_polys) == strong_groebner_basist::resultt::UNSAT) {
      prop.l_set_to_true(const_literal(false));
      return true;
    }
  }
}
```

**File: `src/solvers/algebraic/poly_extract.cpp`**

Add overflow-pattern recognition and wide-ring construction:
```cpp
void poly_extractort::recognise_overflow_patterns(const exprt &e)
{
  e.visit_pre([&](const exprt &x) {
    // Pattern 1: (extract 2N-1 N) (bvmul (zext s) (zext t))
    if (x.id() == ID_extractbits) {
      const auto &eb = to_extractbits_expr(x);
      // Check: lo = bw_main, hi = 2*bw_main - 1, src is bvmul of zext'ed
      if (matches_high_half_pattern(eb)) {
        auto [s, t] = unwrap_zext_bvmul(eb.src());
        introduce_overflow_aux(s, t);
        return;
      }
    }
    // Pattern 2: (bvule (bvmul s t) Y) or similar
    // ... etc ...
  });
}

void poly_extractort::introduce_overflow_aux(const exprt &s, const exprt &t)
{
  // Allocate q_mul, r_mul in wide_extractor's variable index space
  size_t q_idx = wide_extractor.get_var_index("__qmul_" + ...);
  size_t r_idx = wide_extractor.get_var_index("__rmul_" + ...);
  bvmul_overflow_aux[{s, t}] = {q_idx, r_idx};

  // Add the integer-level equation:
  //   s_w * t_w = q_mul * 2^d + r_mul   in ZMod(2^{2d})
  unsigned d_main = bitwidth;
  unsigned d_wide = 2 * d_main;
  auto s_poly = wide_extractor.to_polynomial(s);  // s zero-extended
  auto t_poly = wide_extractor.to_polynomial(t);
  if (!s_poly || !t_poly) return;
  polynomialt q_poly{d_wide, mp_integer{1}, q_idx};
  polynomialt r_poly{d_wide, mp_integer{1}, r_idx};
  mp_integer two_d = power(mp_integer{2}, mp_integer{d_main});
  polynomialt eq = (*s_poly) * (*t_poly) - (q_poly * two_d) - r_poly;
  wide_extractor.side_equations.push_back(eq);

  // Bit-decompose q_mul and r_mul (each d bits in the wide ring
  // since they're < 2^d).
  // Bit-share with main ring: r_mul's bit i equals bvmul(s,t)'s
  // bit i in the main ring. This is the bridge between rings.
  // ... (ensure decompose_bits in main and wide produce consistent
  //      bit variables for the shared canonical-value)
}
```

**File: `src/solvers/algebraic/groebner.cpp`**

No changes — the Buchberger algorithm is ring-agnostic. We just
run it on a different `polynomialt` set with a different
`bitwidth`. All existing soundness guarantees apply.

### B.4 — Soundness: why two-ring reasoning is sound

The bridge between rings is the **bit-decomposition**. For each
expression `e` of bw `d` that we share between rings:

- In the main ring (ZMod(2^d)), `e` is bit-decomposed as
  `e = sum_{i=0..d-1} 2^i b_i`, with `b_i^2 - b_i = 0`.
- In the wide ring (ZMod(2^{2d})), the same expression's
  canonical (d-bit unsigned) value equals `sum_{i=0..d-1} 2^i b_i'`
  with `b_i' = b_i` (same Boolean variable).

The shared bit variables ensure that any model satisfying the
main system's equations also satisfies the wide system's
equations on the canonical-rep parts. The wide-ring overflow
auxiliaries (`q_mul`) are FREE (existentially quantified) — any
model of the main system EXTENDS to a model of the wide system by
choosing `q_mul` appropriately. So:

- **Main system UNSAT** ⇒ formula UNSAT (already established).
- **Wide system UNSAT** ⇒ no extension exists ⇒ formula UNSAT
  (since any model would need to extend the main-system model
  with valid `q_mul`).

The Lean formalisation:
```
formal-proofs/HybridRing.lean:

theorem wide_system_extends_main :
  ∀ model_main : Model (main_system),
    ∃ q_mul_assignment, model_main + q_mul_assignment ⊨ wide_system

theorem wide_unsat_implies_formula_unsat :
  wide_system_unsat → original_formula_unsat
```

### B.5 — Bit-decomposition coordination

The trickiest engineering aspect. The main extractor's
`decompose_bits(e)` and the wide extractor's `decompose_bits(e)`
must produce the SAME bit variable indices for the shared
expressions. Implementation:

```cpp
class shared_bit_decomposition {
  std::map<irep_idt, std::vector<size_t>> shared_bits;

public:
  // Get bits for expression e at bw `b`. If first time, allocate
  // fresh indices. If second time, return same indices.
  std::vector<size_t> get_or_create_bits(
      const exprt &e, unsigned b, poly_extractort &extractor);
};
```

Both extractors share an instance of `shared_bit_decomposition`.
The first one to call `decompose_bits(e)` allocates the indices;
the second reuses.

### B.6 — Range constraints on q_mul, r_mul

Algebraically, we need:
- `0 ≤ q_mul < 2^d` (from `s, t < 2^d` ⇒ `s*t < 2^{2d}` ⇒
  `q_mul < 2^d`)
- `0 ≤ r_mul < 2^d` (canonical mod 2^d)

These ranges are encoded by bit-decomposition: `q_mul = sum_i 2^i
b_(q,i)` for d bits b_(q,i), each idempotent (b^2 = b). This
constrains 0 ≤ q_mul < 2^d in the wide ring (ZMod(2^{2d})).

### B.7 — When to run the wide system

Adding the wide system per-formula is expensive. Gates:
1. Only run if the formula contains a `bvmul` with operands that
   have been zero-extended (the typical overflow-check pattern).
2. Only run if the main system fails to refute (wide is fallback).
3. Cap the wide system size: if more than 5 overflow auxiliaries,
   fall through to bit-blasting (would be too expensive).

## Plan B — total scope and risk

| Item | Lines | Effort | Risk |
|------|-------|--------|------|
| B.1 — Hybrid extractor architecture | ~400 | 1 week | Medium |
| B.2 — Overflow pattern recognition | ~300 | 4 days | Medium |
| B.3 — Bit-decomposition coordination | ~200 | 3 days | High (subtle bugs) |
| B.4 — Wide system run in try_algebraic_solve | ~100 | 2 days | Low |
| B.5 — Lean formalisation (HybridRing.lean) | ~200 | 3 days | Low (case analysis) |
| B.6 — Test suite + benchmarks | — | 3 days | Medium |

**Plan B total**: ~3-4 weeks of focused implementation. Expected
**+5 to +12** SMT-COMP unlocks targeting the bit-level circuit
equivalence cluster (currently 16 benchmarks unsolved in this
cluster).

## Plan B — alternatives considered

### B.alt.1 — Move main system to ZMod(2^{2d}) globally

Drop the d-bit main system; everything lives in ZMod(2^{2d}).

**Pro**: simpler architecture (one ring).
**Con**: doubles every coefficient size, slows down the existing
benchmarks (bw=512 → bw=1024 polynomials), changes the bvmul /
bvudiv encoding semantics. Would regress current 36/66 baseline.

**Verdict**: rejected. The hybrid approach preserves the existing
fast path.

### B.alt.2 — Z-level integer constraint solver

Instead of ZMod(2^{2d}), use an actual integer (Z) constraint
solver alongside ZMod(2^d).

**Pro**: more powerful (handles ranges, divisibility, etc.
naturally).
**Con**: requires new solver (Presburger / linear arithmetic
over Z), significant integration cost, architecturally heavier
than ZMod(2^{2d}).

**Verdict**: deferred. ZMod(2^{2d}) is sufficient for the
bvmul-overflow patterns we target. Z-level can be a future
extension if needed.

### B.alt.3 — Bit-level multiplier circuit reasoning

Instead of overflow auxiliaries, encode the bit-level multiplier
circuit (O(d^2) constraints per multiplication) and reason at the
Boolean level.

**Pro**: theoretically complete for any bvmul reasoning.
**Con**: O(d^2) explosion. For d=512, 262k constraints per mult.
Buchberger would not handle this.

**Verdict**: rejected. Doesn't scale.

## Plan B — risks and mitigations

1. **Bit-decomposition coordination is subtle** (B.3). A bug
   here means main and wide systems disagree on shared variables,
   producing INCORRECT (unsound) refutations.
   - Mitigation: extensive Lean formalisation of the bridging
     theorem (`wide_system_extends_main`).
   - Mitigation: comprehensive unit tests with synthetic
     bvmul-overflow examples (manual verification of refutations).

2. **Wide-system Buchberger may be slow** (B.5). Polynomials in
   ZMod(2^{2d}) have larger coefficients; the basis can grow
   larger. With d=512, the wide ring is 1024 — coefficients are
   1024-bit integers.
   - Mitigation: gate by overflow-pattern presence (only fire
     when likely to help).
   - Mitigation: cap on wide-system size (≤5 overflow aux).
   - Mitigation: use Plan A's pair-selection (normal selection)
     in the wide system too.

3. **Bit-blasting interaction** (similar to Phase 2.6's crash):
   the wide system might trigger get_literals on shared
   expressions with mismatched widths.
   - Mitigation: avoid materialise_bit_alignments and
     host_substitutions in the wide-system Buchberger; use a
     dedicated, bare-bones refutation path (similar to Phase
     2.6's standalone Tseitin refutation).

4. **The benchmarks I expect to unlock might need MORE than just
   wide-ring reasoning**. brummayerbiere2_*ulov* requires
   equivalence between the high half of bvmul AND a complex
   AND/OR tree of Boolean operators. Plan B handles the first
   half; the second still needs bit-level reasoning.
   - Mitigation: focus on the simpler bvmul-overflow-only
     benchmarks first (e.g., parts of log-slicing_bv*div*).
     brummayerbiere2_*ulov* may need additional bit-level
     reasoning that's out of Plan B's scope.

## Plan B — Lean formalisation

New module: `formal-proofs/HybridRing.lean`

```lean
import Mathlib.RingTheory.Ideal.Basic

/-- The bridging theorem: a model of the main system in
    ZMod(2^d) extends to a model of the wide system in ZMod(2^{2d})
    by choosing q_mul = (s.val * t.val) / 2^d. -/
theorem wide_system_extends_main
  (d : ℕ) (model_main : ZMod (2^d) → Bool)
  (s t : ZMod (2^d)) (s_lifted t_lifted : ZMod (2^(2*d)))
  (hs : (s.val : ZMod (2^(2*d))) = s_lifted)
  (ht : (t.val : ZMod (2^(2*d))) = t_lifted)
  : ∃ (q_mul r_mul : ZMod (2^(2*d))),
      r_mul.val < 2^d ∧
      q_mul.val < 2^d ∧
      s_lifted * t_lifted = q_mul * (2^d : ZMod (2^(2*d))) + r_mul ∧
      r_mul.val = (s.val * t.val) % 2^d  -- bridges to main system

/-- Soundness: if the wide system is unsatisfiable, the original
    formula is unsatisfiable. -/
theorem wide_unsat_implies_formula_unsat
  (wide_polys : List (Polynomial (ZMod (2^(2*d)))))
  (h_unsat : (∀ model, ¬model ⊨ wide_polys))
  : ∀ model_main, ¬model_main ⊨ original_formula
```

Effort: ~3 days (case analysis + bit-decomposition lemmas already
in `formal-proofs/StrongGB.lean`).

## Plan B — paper impact

If Plan B unlocks +5-12 SMT-COMP benchmarks, the paper updates:
- §empirical: from 36/66 to 41-48/66 (~14-18% improvement).
  Combined with Plan A: 41-48 + 5-8 ≈ 46-56/66.
- §technique: new section on "Hybrid Z/ZMod polynomial reasoning
  for bit-vector overflow". Discuss the wide-ring extension, the
  bit-bridge, and the soundness story.
- §future-work: Z-level integer constraint solving (B.alt.2).

The hybrid Z/ZMod design is novel — the standard SMT bv-solving
approaches either bit-blast everything (fast for narrow widths)
or use entirely separate algorithms (e.g., int-blasting in CVC5).
A hybrid that maintains TWO polynomial systems with shared
bit-variables, where each ring can independently refute the
formula, is a research contribution.

## Plan B — summary

Plan B is a **major architectural extension** (~3-4 weeks). It
introduces a SECOND polynomial system in a wider ring (ZMod(2^{2d}))
that handles bvmul-overflow reasoning. The two systems share
bit-variables to coordinate the canonical-rep view of expressions.

Expected impact: +5 to +12 SMT-COMP unlocks targeting the bit-
level circuit equivalence cluster.
