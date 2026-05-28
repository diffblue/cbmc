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
| `groebner.cpp::compute` (UNSAT detection sound) | `StrongGB.lean::two_trick_unsat_sound` | DONE |
| `groebner.cpp::compute` (naive completeness false) | `StrongGB.lean::naive_completeness_is_false` | DONE |
| `groebner.cpp::compute` (refined saturation completeness) | `StrongGB.lean::two_trick_saturation_complete` | STATEMENT-ONLY |
| `boolbv.cpp::set_to`/`finish_eager_conversion` (defer/replay) | `Defer.lean::defer_replay_equivalence` | DONE-MOD-AXIOMS |

## Status legend

- **DONE**: theorem fully proven (zero `sorry`, no module-specific axioms beyond mathlib).
- **DONE-MOD-AXIOMS**: theorem fully proven (zero `sorry`) relative to a small set of explicit axioms in the module; the axioms capture properties of the implementation pipeline that would require formalising the operational semantics of the boolbv layer or the strong-GB algorithm to prove from first principles.
- **STATEMENT-ONLY**: precise Lean statement of the claim is present; the proof is admitted (`sorry`). The module docstring documents the decomposition needed to fill in the proof.

The two non-DONE entries:

- `two_trick_saturation_complete` (STATEMENT-ONLY): the strong-GB completeness theorem of Song et al. (TACAS 2024) under the `WellFormedEncoding` hypothesis. **Important note**: a related theorem (`naive_completeness_is_false`) is fully proven in `StrongGB.lean`, demonstrating with a concrete counterexample (`d=2`, `n=0`, `F={C 2}`) that the *naive* completeness statement (without `WellFormedEncoding`) is FALSE. The refined version requires F to have the structural properties of the BV-formula encoding; mechanising it requires (a) a formal definition of the BV-encoding function, and (b) the five-step decomposition documented in `StrongGB.lean`'s docstring (extended division algorithm, 2-trick step, termination, soundness, and the deep completeness step). Estimated 1–6 months of focused Lean work, comparable to a master's thesis.

- `defer_replay_equivalence` (DONE-MOD-AXIOMS): the deferred-bit-blasting pipeline equivalence. Proven via induction on the assertion list from two semantic axioms (A1: `defer_finish_eq_eager_finish`; A2: `finish_eager_commutes`) reflecting the implementation's invariants. Mechanising the axioms themselves would require modelling the boolbv layer's operational semantics (~1-2 weeks of follow-on work).

## Mathlib-contributable lemmas

The `StrongGB.lean::MathlibCandidates` namespace contains general-purpose facts about `ZMod (2^d)` that are not specific to the strong-GB context:

- `isUnit_of_odd_nat_in_two_pow`: an odd natural number is a unit in `ZMod (2^d)`.
- `isUnit_iff_two_not_dvd_val`: a `ZMod (2^d)` element is a unit iff its lift to `ℕ` is odd.

Additional candidates (not yet in MathlibCandidates):

- `IsLocalRing (ZMod (p^n))` for prime `p` and `n ≥ 1`. This is a clean, self-contained instance that mathlib does not currently have.
- `Re4.lean::frobenius_pow_eq_self` is a useful 2-adic-valuation fact that could be generalised.

## Verification

The proofs build with `lake build` in `formal-proofs/`. CI integration
ensures the proofs continue to compile when implementation changes are
made; if a theorem's IMPL line points to deleted/renamed code, the
build fails the lint stage.
