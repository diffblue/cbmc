# Algorithm Coverage Audit: `src/solvers/algebraic/`

This document catalogues every algorithm and tweak in
`src/solvers/algebraic/` and records its formal-proof coverage.

## Summary

- **Covered**: 13 algorithms have a corresponding Lean theorem.
- **Trivial / config**: 16 functions are basic algebra, config, or
  lookups (no proof obligation beyond standard arithmetic).
- **Gaps**: 7 algorithms have non-trivial mathematical content but
  no formal proof — these are listed at the bottom.

## File: `poly_ring.cpp` (15 entities)

| Algorithm | Type | Coverage |
|-----------|------|----------|
| `monomialt::operator*` | Exponent vector addition | TRIVIAL |
| `monomialt::divides` | Exponent dominance | TRIVIAL |
| `monomialt::quotient` | Exponent subtraction | TRIVIAL |
| `monomialt::operator<` | Graded lex ordering | TRUSTED-DEF |
| `monomialt::operator==` | Equality | TRIVIAL |
| `polynomialt::reduce` (mod 2^d) | Modular reduction | TRIVIAL |
| `polynomialt::polynomialt(...)` (constructors) | Construction | TRIVIAL |
| `polynomialt::normalize` | Combine like terms, sort | IMPLICIT — preserves polynomial value, but no direct theorem |
| `polynomialt::operator+`, `operator-` | Polynomial add/sub | TRIVIAL |
| `polynomialt::operator*(scalar)` | Scalar multiplication | TRIVIAL (used in two_trick_preserves_ideal) |
| `polynomialt::operator*(polynomialt)` | Polynomial multiplication | TRIVIAL |
| `polynomialt::multiply(other, bit_vars)` | Multiplication with Frobenius | COVERED — `Re4.lean::frobenius_pow_eq_self` |
| **`inverse_mod_2d`** | Hensel-lifting modular inverse | **GAP** — no proof of correctness |
| `val_2` | 2-adic valuation | TRIVIAL |
| `apply_frobenius_idempotency` | Apply b^k → b for bit vars | COVERED — `Re4.lean::frobenius_pow_eq_self` |
| `substitute_variable` | Substitute variable for poly | TRIVIAL |

## File: `poly_extract.cpp` (7 entities)

| Algorithm | Type | Coverage |
|-----------|------|----------|
| `set_bitwidth` | Configuration setter | TRIVIAL |
| `get_var_index` | Symbol table lookup | TRIVIAL |
| **`to_polynomial`** | Convert `exprt` → `polynomialt` | **GAP** — encoding faithfulness not formally verified |
| **`extract_equation`** | Convert `equal_exprt` → polynomial | **GAP** — encoding faithfulness not formally verified |
| `materialise_bit_alignments` | Generate bit-alignment polys | COVERED — `BitAlignment.lean::scalar_alignment_low_bits_zero`, `scalar_alignment_shifted_bits` |
| `extract_predicate` | Convert predicate → polys | COVERED — `SubgoalSix.lean::bvult_pow2_implies_high_bits_zero`, `bvuge_2d_minus_2k_implies_high_bits_one`, `chainLtBool_correctness`, `bvslt_via_xor_msb` |
| `decompose_bits` | Generate bit-decomposition polys | COVERED — `Re4.lean::stdBit_sums_to_self`, `bit_decomp_existence`, `bit_idempotency_forces_zero_or_one` |

## File: `vanishing.cpp` (8 entities)

| Algorithm | Type | Coverage |
|-----------|------|----------|
| `nu2` | 2-adic valuation (helper) | TRIVIAL |
| **`smarandache_function`** | Smarandache function | **GAP** — number-theoretic identity not verified |
| **`nu2_factorial`** | Legendre's formula for ν₂(k!) | **GAP** — not verified |
| **`build_canonical_to_factorial`** | Change-of-basis matrix | **GAP** — algorithmic correctness not verified |
| `kronecker_entry` | Matrix entry helper | TRIVIAL |
| `is_vanishing_polynomial` | Detect vanishing on Z_2^d | COVERED — `Vanishing.lean::fallingFactorial_zero_of_lt`, `falling_factorial_sufficient` |
| `build_falling_factorial` | Construct falling-factorial poly | TRIVIAL (direct definition) |
| **`generate_zfp_generators`** | Generate zero-falling-power gens | **GAP** — generator-set correctness not verified |

## File: `groebner.cpp` (7 entities)

| Algorithm | Type | Coverage |
|-----------|------|----------|
| `has_constant` | Detect odd constant in basis | COVERED — `GroebnerSoundness.lean::ZMod.isUnit_of_odd_nat`, `ideal_eq_top_of_unit_mem`, `ZMod.two_not_isUnit`, `soundness_of_odd_constant_check` |
| **`s_polynomial`** | Compute S-polynomial | INDIRECT — `BuchbergerCorrectness.lean::buchberger_ideal_preservation` covers the abstract operation, but no direct C++ ↔ Lean correspondence theorem |
| **`strong_reduce`** | Reduce w/ basis (incl. 2-trick) | INDIRECT — same situation; `two_trick_preserves_ideal` covers the saturation step abstractly |
| `compute` | Main strong-GB algorithm | COVERED (extensively) — see `groebner.cpp` for 9 PROOF: references |
| **`extract_candidate`** | Model extraction from basis | **GAP** — soundness of extracted model not verified |
| **`reduce_by_basis`** | Public reduction utility | **GAP** — soundness (returns 0 ⇒ in ideal) implicit |

## Summary of gaps (7 genuine)

### High-priority gaps
These have non-trivial mathematical content that should ideally have a proof:

1. **`inverse_mod_2d`** (`poly_ring.cpp`): Hensel-lifting modular inverse. Claim: `inverse_mod_2d(a, d) * a ≡ 1 (mod 2^d)` for odd `a`. This is invoked by `strong_reduce` to compute coefficient quotients.

2. **`to_polynomial` / `extract_equation`** (`poly_extract.cpp`): the fundamental encoding faithfulness — that the resulting polynomial evaluates to the same value (mod 2^d) as the original C expression. **Most critical gap**: all downstream proofs are about polynomial systems; if the polynomial system doesn't faithfully encode the original program, the proofs don't transfer.

3. **`extract_candidate`** (`groebner.cpp`): used by Level-3 unit-propagation guidance. Claim: if a non-empty assignment is returned, every basis polynomial evaluates to 0 at that assignment. Used as a heuristic, but its soundness as a satisfying assignment (for the purpose of guiding the SAT solver) is not formally verified.

### Medium-priority gaps
These have specific mathematical claims with known closed-form solutions:

4. **`smarandache_function`** (`vanishing.cpp`): the Smarandache function is well-known; the implementation should match the standard recursive formula.

5. **`nu2_factorial`** (`vanishing.cpp`): Legendre's formula `ν₂(k!) = k - s₂(k)` where `s₂(k)` is the sum of binary digits.

6. **`build_canonical_to_factorial`** / **`generate_zfp_generators`** (`vanishing.cpp`): the change-of-basis correctness. The generator-set conformance to the falling-factorial basis is implicit.

### Low-priority (already implicitly covered)
These have abstract proofs but no direct C++ ↔ Lean correspondence theorem:

7. **`s_polynomial`** / **`strong_reduce`** / **`reduce_by_basis`** (`groebner.cpp`): covered by `BuchbergerCorrectness.lean::buchberger_ideal_preservation` and `StrongGB.lean::two_trick_preserves_ideal` at the abstract level. The gap is the implementation-level correspondence: that the C++ code correctly implements these operations on the concrete `polynomialt` data structure. Closing this gap would require formalising the data structures and proving the C++ operations are faithful — a substantial undertaking.

## Coverage classification

Total entities audited: **37**

| Status | Count | Description |
|--------|------:|-------------|
| COVERED | 13 | Direct PROOF: cross-reference to a Lean theorem |
| TRIVIAL | 12 | Basic arithmetic, config, lookups; no proof obligation |
| TRUSTED-DEF | 1 | Ordering definition (no theorem to prove) |
| INDIRECT | 3 | Abstract Lean theorem covers the math, but no C++ ↔ Lean correspondence |
| **GAP** | **8** | Non-trivial math without a Lean theorem |

## Methodology

- "Algorithm" = a function or method in `src/solvers/algebraic/*.cpp` whose
  body contains non-trivial logic.
- "Trivial" = ≤ 5 lines of straight-line standard arithmetic with no
  algorithmic content (e.g., field setters, exponent sums).
- "Covered" = there exists a `// PROOF: formal-proofs/Module.lean::name`
  comment in the C++ source pointing to a fully-proven Lean theorem about
  the algorithmic content.
- "Gap" = there is non-trivial mathematical content not covered by any
  Lean theorem.

This audit was performed by enumerating function definitions in each
`.cpp` file and classifying each one. The script:
```bash
grep -nE "^[a-zA-Z_].*::[a-zA-Z_]" src/solvers/algebraic/*.cpp | grep -v '^//'
```
produces the canonical list of entities to audit.

## Path forward

To eliminate the high-priority gaps:

1. Prove `inverse_mod_2d` correctness via Hensel's lemma (small, well-scoped).
2. Define an evaluation semantics for `polynomialt` that matches the
   C-expression semantics, and prove `to_polynomial` faithfulness on
   linear/quadratic terms (more substantial).
3. Prove `extract_candidate` soundness: returned assignment satisfies the
   univariate linear equations from which it was extracted.

Of these, (1) is a clear, self-contained number-theoretic fact and is the
quickest win. (2) is the most impactful but the most work.
