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
| `poly_ring.cpp::inverse_mod_2d` | `PolyRing.lean::inverse_mod_2d_correct` | DONE |
| `poly_ring.cpp::monomialt::operator<` | `PolyRing.lean::grevlexLt_irrefl`, `grevlexLt_asymm`, `grevlexLt_total` | DONE |
| `poly_ring.cpp::polynomialt::normalize` | `PolyRing.lean::normalize_combine_like_terms`, `normalize_drop_zero_preserves_sum` | DONE |
| `poly_extract.cpp::decompose_bits` (idempotency emission) | `Re4.lean::bit_idempotency_forces_zero_or_one` | DONE |
| `poly_extract.cpp::decompose_bits` (sum-decomposition emission) | `Re4.lean::stdBit_sums_to_self`, `bit_decomp_existence` | DONE |
| `poly_ring.cpp::polynomialt::multiply` (bit_vars overload) | `Re4.lean::frobenius_pow_eq_self` | DONE |
| `poly_extract.cpp::to_polynomial` | `Encoding.lean::toPolynomial_eval`, `cast_value_preserved_across_widths`, `reduce_value_preserved_across_widths` | DONE |
| `poly_extract.cpp::extract_equation` | `Encoding.lean::extract_equation_iff`, `encodeEquations_satisfiable_iff` | DONE |
| `smt2_parser.cpp::bv_division` (x/x rewrite) | `DivisionRewrites.lean::bvudiv_self` | DONE |
| `smt2_parser.cpp::bv_division` (0/x rewrite) | `DivisionRewrites.lean::bvudiv_zero_left` | DONE |
| `smt2_parser.cpp::bv_mod` (x%x rewrite) | `DivisionRewrites.lean::bvurem_self` | DONE |
| `smt2_parser.cpp::bv_mod` (0%x rewrite) | `DivisionRewrites.lean::bvurem_zero_left` | DONE |
| `smt2_parser.cpp::try_bvurem_relation_rewrite` (bvule rewrite) | `DivisionRewrites.lean::bvule_bvurem_self` | DONE |
| `smt2_parser.cpp::try_bvurem_relation_rewrite` (bvult rewrite) | `DivisionRewrites.lean::bvult_bvurem_self` | DONE |
| `smt2_parser.cpp::bv_division` (ite-distribution) | `DivisionRewrites.lean::bvudiv_ite_distribution` | DONE |
| `smt2_parser.cpp::bv_mod` (ite-distribution) | `DivisionRewrites.lean::bvurem_ite_distribution` | DONE |
| `smt2_parser.cpp::bv_division` (cancellation: bvudiv (bvurem A y) y) | `DivisionRewrites.lean::bvudiv_bvurem_self` | DONE |
| `smt2_parser.cpp::bvmul_with_simplifications` (ite-distribution + folding) | `DivisionRewrites.lean::bvmul_ite_distribution`, `bvmul_zero_right`, `bvmul_one_right`, `bvmul_neg_one_right` | DONE |
| `poly_ring.cpp::karatsuba_multiply` (Karatsuba 3-mult identity) | `Karatsuba.lean::karatsuba_identity`, `karatsuba_multiply_correct` | DONE |
| `poly_extract.cpp::to_polynomial` (bvudiv/bvurem polynomial encoding) | `BvDivPolyEncoding.lean::bvdiv_bvurem_polynomial_eq`, `bvurem_zero_polynomial_eq`, `bvdiv_polynomial_overapprox` | DONE |
| `poly_extract.cpp::to_polynomial` (bvnot direct algebraic form) | `BvDivPolyEncoding.lean::bvnot_eq_neg_one_sub` | DONE |
| `boolbv.cpp::set_to` (nonzero fast-path: bvult 0 x ⇒ algebraic_disequalities) | `BvDivPolyEncoding.lean::NonzeroFastPath::bvult_zero_iff_ne_zero`, `bvuge_one_iff_ne_zero` | DONE |
| `smt2_parser.cpp::apply_cond_eq_substitution` (if-condition propagation) | `IteCondPropagation.lean::if_cond_propagation` | DONE |
| `smt2_parser.cpp::binary_predicate` (push equal/notequal/le/lt through ite) | `IteCondPropagation.lean::predicate_through_ite_left`, `eq_through_ite_left`, `notequal_through_ite_left`, `le_through_ite_left`, `lt_through_ite_left` | DONE |
| `tseitin_propagation.cpp::tseitin_propagatort::enforce` (backward inversion through bitnot/bitor/bitand/bitxor/equal/notequal) | `TseitinPropagation.lean::bitnot_inversion`, `bitor_zero_inversion`, `bitand_one_inversion`, `bitxor_inversion`, `eq_true_inversion`, `eq_false_inversion` | DONE |
| `tseitin_propagation.cpp::tseitin_propagatort::evaluate` (forward simplification of boolean atoms) | `TseitinPropagation.lean::bitor_eval`, `bitor_eval_both_false` | DONE |
| `boolbv.cpp::try_algebraic_solve` (Tseitin-discovered bv-equality / bv-disequality emission) | `TseitinPropagation.lean::bv_eq_emission`, `bv_neq_emission` | DONE |
| `poly_extract.cpp::to_polynomial` (concatenation polynomial encoding) | `TseitinPropagation.lean::concat_polynomial_encoding` | DONE |
| `poly_extract.cpp::extract_predicate` (power-of-2 upper bound) | `SubgoalSix.lean::bvult_pow2_implies_high_bits_zero` | DONE |
| `poly_extract.cpp::extract_predicate` (lower bound 2^d - 2^k) | `SubgoalSix.lean::bvuge_2d_minus_2k_implies_high_bits_one` | DONE |
| `poly_extract.cpp::extract_predicate` (bit-comparator chain) | `SubgoalSix.lean::chainLtBool_correctness` | DONE |
| `poly_extract.cpp::extract_predicate` (signed via XOR) | `SubgoalSix.lean::bvslt_via_xor_msb` | DONE |
| `poly_extract.cpp::materialise_bit_alignments` (low bits zero) | `BitAlignment.lean::scalar_alignment_low_bits_zero` | DONE |
| `poly_extract.cpp::materialise_bit_alignments` (shifted bits) | `BitAlignment.lean::scalar_alignment_shifted_bits` | DONE |
| `vanishing.cpp::nu2_factorial` | `Vanishing.lean::nu2Factorial_eq_padicVal` | DONE |
| `vanishing.cpp::smarandache_function` | `Vanishing.lean::smarandache_iff_nu2Factorial`, `smarandache_exists` | DONE |
| `vanishing.cpp::build_canonical_to_factorial` | `Vanishing.lean::stirlingSecond_recurrence`, `stirlingSecond_diag`, `stirlingSecond_zero_of_lt` | DONE |
| `vanishing.cpp::generate_zfp_generators` | `Vanishing.lean::zfpCoeff_mul_factorial_divisible` | DONE |
| `vanishing.cpp::is_vanishing_polynomial` (falling factorial) | `Vanishing.lean::fallingFactorial_zero_of_lt` | DONE |
| `vanishing.cpp::is_vanishing_polynomial` (sufficient condition) | `Vanishing.lean::falling_factorial_sufficient` | DONE |
| `groebner.cpp::s_polynomial` | `BuchbergerCorrectness.lean::s_poly_in_ideal` | DONE |
| `groebner.cpp::strong_reduce` | `BuchbergerCorrectness.lean::reduce_in_ideal`, `scale_in_ideal`; `StrongGB.lean::two_trick_preserves_ideal` | DONE |
| `groebner.cpp::reduce_by_basis` | `BuchbergerCorrectness.lean::reduce_in_ideal` | DONE |
| `groebner.cpp::extract_candidate` | `ExtractCandidate.lean::extract_candidate_local_soundness`, `solve_univariate_linear_unit` | DONE |
| `groebner.cpp::compute` (2-trick preserves ideal) | `StrongGB.lean::two_trick_preserves_ideal`, `two_trick_preserves_ideal_mv` | DONE |
| `groebner.cpp::compute` (UNSAT detection sound) | `StrongGB.lean::two_trick_unsat_sound` | DONE |
| `groebner.cpp::compute` (progress-tracking invariant) | `BuchbergerTermination.lean::progress_invariant_preserved`, `counter_exceeds_baseline_implies_empty`, `buggy_step_breaks_invariant` | DONE |
| `groebner.cpp::has_constant` (odd ⇒ unit) | `GroebnerSoundness.lean::ZMod.isUnit_of_odd_nat` | DONE |
| `groebner.cpp::has_constant` (unit ⇒ ideal=⊤) | `GroebnerSoundness.lean::ideal_eq_top_of_unit_mem` | DONE |
| `groebner.cpp::has_constant` (2 not unit) | `GroebnerSoundness.lean::ZMod.two_not_isUnit` | DONE |
| `groebner.cpp::has_constant` (top-level soundness) | `GroebnerSoundness.lean::soundness_of_odd_constant_check` | DONE |
| `groebner.cpp::compute` (idempotency ⇒ Boolean) | `Re4.lean::all_idempotent_to_bool` | DONE |
| `groebner.cpp::compute` (naive completeness false) | `StrongGB.lean::naive_completeness_is_false` | DONE |
| `groebner.cpp::compute` (d=1 completeness) | `StrongGB.lean::d_eq_one_completeness` | DONE |
| `groebner.cpp::compute` (idempotent ⇒ {0,1}) | `StrongGB.lean::sq_eq_self_of_zmod_two_pow` | DONE |
| `groebner.cpp::compute` (refined completeness fails) | `StrongGB.lean::two_trick_saturation_complete_is_false` | DONE |
| `groebner.cpp::select_next_pair` (pair selection orthogonal to soundness) | `StrongGB.lean::pair_selection_orthogonal` | DONE |
| `groebner.cpp::full_reduce` (tail-reduction step preserves ideal) | `StrongGB.lean::tail_reduction_in_ideal` | DONE |
| `groebner.cpp::interreduce_basis` (basis interreduction preserves ideal) | `StrongGB.lean::interreduce_preserves_ideal` | DONE |
| `boolbv.cpp::walk_for_algebraic` (leaf implication soundness) | `AlgebraicTreeWalk.lean::leaf_implied_by_walk_and`, `leaf_implied_by_walk_not_or`, `leaf_implied_by_walk_not`, `walk_chain_sound` | DONE |
| `boolbv.cpp::walk_for_algebraic` (IF-rebuild equivalence) | `AlgebraicTreeWalk.lean::if_rebuild_equivalence`, `if_rebuild_lr_equivalence` | DONE |
| `boolbv.cpp::set_to`/`finish_eager_conversion` (defer/replay states) | `Defer.lean::defer_replay_equivalence` | DONE |
| `boolbv.cpp::try_algebraic_solve` (verdict equivalence) | `Defer.lean::defer_verdict_equivalence` | DONE |
| `boolbv.cpp::try_algebraic_solve` (verdict from empty state) | `Defer.lean::defer_verdict_from_empty` | DONE |

## Status legend

- **DONE**: theorem fully proven (zero `sorry`, no module-specific axioms beyond standard mathlib axioms `propext` and `Quot.sound`).

(Historical note: an earlier revision of `Defer.lean` postulated two semantic axioms — `defer_finish_eq_eager_finish` (A1) and `finish_eager_commutes` (A2) — that captured properties of the boolbv layer's operational semantics. The current revision uses a concrete set-based abstract model (`SolverState` as a pair of (committed, deferred) sets) under which both A1 and A2 are provable theorems by union associativity / commutativity. The defer-replay equivalence and verdict-equivalence theorems are now `DONE` outright; no project-specific axioms remain.)

## Why there is no `two_trick_saturation_complete` theorem

The strong-GB algorithm in `groebner.cpp::compute` is **sound but not complete**: it returns `UNSAT` only when an odd constant is found, and `UNKNOWN` otherwise. The implementation makes no completeness claim, and we proved formally that none can be made under reasonable hypotheses:

- `naive_completeness_is_false`: the naive statement "F unsat ⇒ odd constant in Ideal.span F" is false.
- `two_trick_saturation_complete_is_false`: even adding idempotency on each variable (the natural well-formedness hypothesis) does not make completeness hold — the same counterexample {C 2} defeats it.

Mechanising the actual Song et al. (TACAS 2024) completeness theorem would require defining a formal `BVFormula → Polynomial` encoding and proving that the resulting polynomial systems have specific structural properties (beyond just idempotency). This is ~1–6 months of focused work and is **not required by the implementation**, which intentionally permits UNKNOWN.

## Bi-directional traceability audit

As of the most recent revision the table above is bi-directionally consistent:

- **Forward (C++ → Lean)**: every `// PROOF: formal-proofs/Module.lean::theorem_name` reference in `src/` resolves to a theorem with that exact name in the corresponding Lean file. Verified mechanically by:
  ```
  grep -rh "PROOF: formal-proofs" src/ | sort -u | while read ref; do
    file=$(echo "$ref" | sed 's|.*formal-proofs/\([^:]*\)::.*|\1|')
    thm=$(echo "$ref" | sed 's|.*::\([^ ]*\).*|\1|')
    grep -qE "^(theorem|lemma|def|axiom|instance) +$thm\b" "formal-proofs/$file" \
      || echo "MISS $file::$thm"
  done
  ```

- **Backward (Lean → C++)**: every contract-level theorem in the Lean modules is referenced from the corresponding implementation site. The Lean modules also contain (as expected) internal helper lemmas, mathlib-contribution candidates, and stepping-stone results that legitimately have no `src/` reference. The breakdown:

  | Category | Count | Referenced |
  |----------|------:|-----------:|
  | Contract-level theorems | 28 | 28 |
  | Internal helpers | ~13 | n/a |
  | Mathlib candidates | 4 | n/a |
  | Auxiliary (BuchbergerCorrectness, GroebnerSoundness internals) | ~11 | n/a |

  All 28 contract-level theorems carry a matching `// PROOF:` comment in the implementation.

## Mathlib-contributable lemmas

The `StrongGB.lean::MathlibCandidates` namespace contains general-purpose facts about `ZMod (2^d)` that are not specific to the strong-GB context:

- `isUnit_of_odd_nat_in_two_pow`: an odd natural number is a unit in `ZMod (2^d)`.
- `isUnit_iff_two_not_dvd_val`: a `ZMod (2^d)` element is a unit iff its lift to `ℕ` is odd.
- `not_isUnit_iff_prime_dvd_val`: in `ZMod (p^n)`, a non-unit has `p | val`.
- `isLocalRing_ZMod_prime_pow`: `IsLocalRing (ZMod (p^n))` for prime `p` and `n ≥ 1`. The unique maximal ideal is `(p)`.

Additionally, `StrongGB.lean::sq_eq_self_of_zmod_two_pow` (outside the namespace) proves that `x^2 = x` in `ZMod (2^d)` implies `x = 0 ∨ x = 1`. This generalises `eq_zero_or_one_of_sq_eq_self` (which requires `CancelMonoidWithZero`) to the non-domain `ZMod (2^d)`.

Additional candidates (not yet formalised):

- `Re4.lean::frobenius_pow_eq_self` is a useful 2-adic-valuation fact that could be generalised.

## Verification

The proofs build with `lake build` in `formal-proofs/`. CI integration
ensures the proofs continue to compile when implementation changes are
made; if a theorem's IMPL line points to deleted/renamed code, the
build fails the lint stage.
