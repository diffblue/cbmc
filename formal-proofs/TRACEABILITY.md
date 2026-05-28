# Bi-directional Traceability: Lean Proofs ↔ Implementation

This document records the mapping between formal-proof obligations
(in `formal-proofs/`) and the implementation that satisfies them
(in `src/solvers/algebraic/` and `src/solvers/flattening/boolbv.cpp`).

## Conventions

### Lean → Implementation
Each Lean theorem that mechanises a soundness claim about a specific
piece of the implementation carries a Doxygen-style comment of the
form:
```
/-- IMPL: src/solvers/algebraic/poly_extract.cpp::function_name (lines)
    DESCRIPTION: short prose ...
-/
theorem foo : ... := by ...
```

### Implementation → Lean
Each implementation site that has a corresponding formal proof
carries a comment of the form:
```cpp
// PROOF: formal-proofs/Module.lean::theorem_name
//        Soundness witness for the encoding/transformation below.
```

### Cross-reference table
This document records the full mapping. Each row pairs an
implementation site with one or more Lean theorems.

## Mapping Table

| Implementation Site | Formal Proof | Status |
|---------------------|--------------|--------|
| `poly_ring.cpp::apply_frobenius_idempotency` | `Re4.lean::frobenius_pow_eq_self` | DONE |
| `poly_extract.cpp::decompose_bits` (idempotency emission) | `Re4.lean::bit_idempotency_forces_zero_or_one` | DONE |
| `poly_extract.cpp::decompose_bits` (sum-decomposition emission) | `Re4.lean::stdBit_sums_to_self`, `bit_decomp_existence` | DONE |
| `poly_ring.cpp::polynomialt::multiply` (bit_vars overload) | `Re4.lean::frobenius_pow_eq_self` | DONE |
| `poly_extract.cpp::extract_predicate` (power-of-2 upper bound) | `SubgoalSix.lean::bvult_pow2_implies_high_bits_zero` | DONE |
| `poly_extract.cpp::extract_predicate` (lower bound 2^d - 2^k) | `SubgoalSix.lean::bvuge_2d_minus_2k_implies_high_bits_one` | DONE |
| `poly_extract.cpp::extract_predicate` (bit-comparator chain) | `SubgoalSix.lean::chainLtBool_correctness` | DONE |
| `poly_extract.cpp::extract_predicate` (signed via XOR) | `SubgoalSix.lean::bvslt_via_xor_msb` | DONE |
| `poly_extract.cpp::materialise_bit_alignments` (low bits zero) | `BitAlignment.lean::scalar_alignment_low_bits_zero` | DONE |
| `poly_extract.cpp::materialise_bit_alignments` (shifted bits) | `BitAlignment.lean::scalar_alignment_shifted_bits` | DONE |
| `vanishing.cpp::is_vanishing_polynomial` (falling factorial) | `Vanishing.lean::fallingFactorial_zero_of_lt` | DONE |
| `vanishing.cpp::is_vanishing_polynomial` (sufficient condition) | `Vanishing.lean::falling_factorial_sufficient` | DONE |
| `groebner.cpp::compute` (2-trick preserves ideal) | `StrongGB.lean::two_trick_preserves_ideal`, `two_trick_preserves_ideal_mv` | DONE |
| `groebner.cpp::compute` (UNSAT detection sound) | `StrongGB.lean::two_trick_unsat_sound`, `unsat_implies_ideal_top` | DONE-MOD-AXIOMS |
| `groebner.cpp::compute` (saturation completeness) | `StrongGB.lean::two_trick_saturation_complete` | STATEMENT-ONLY |
| `boolbv.cpp::set_to`/`finish_eager_conversion` (defer/replay) | `Defer.lean::defer_replay_equivalence` | DONE-MOD-AXIOMS |

## Status legend

- **DONE**: theorem fully proven (zero `sorry`, no module-specific axioms beyond mathlib).
- **DONE-MOD-AXIOMS**: theorem fully proven (zero `sorry`) relative to a small set of explicit axioms in the module; the axioms capture properties of the implementation pipeline that would require formalising the operational semantics of the boolbv layer or the strong-GB algorithm to prove from first principles.
- **STATEMENT-ONLY**: precise Lean statement of the claim is present; the proof is admitted (`sorry`). The module docstring documents the decomposition needed to fill in the proof.

The two non-DONE entries:

- `two_trick_saturation_complete` (STATEMENT-ONLY): the strong-GB completeness theorem of Song et al. (TACAS 2024). Requires (a) extension of mathlib's `MonomialOrder.div` past the unit-leading-coefficient hypothesis, (b) formalisation of the 2-trick saturation step, (c) termination over `ZMod (2^d)`, (d) soundness, (e) the deep completeness step (~master's-thesis-scale work). The `unsat_implies_ideal_top` corollary is proven from this conditionally.

- `defer_replay_equivalence` (DONE-MOD-AXIOMS): the deferred-bit-blasting pipeline equivalence. Proven via induction on the assertion list from two semantic axioms (A1: `defer_finish_eq_eager_finish`; A2: `finish_eager_commutes`) reflecting the implementation's invariants. Mechanising the axioms themselves would require modelling the boolbv layer's operational semantics (~1-2 weeks of follow-on work).

## Verification

The proofs build with `lake build` in `formal-proofs/`. CI integration
ensures the proofs continue to compile when implementation changes are
made; if a theorem's IMPL line points to deleted/renamed code, the
build fails the lint stage.
