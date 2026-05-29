/-
Soundness of pushing equality / disequality / relational predicates
through `ite`, with substitution of the if-condition's equalities
into the true branch.

The C++ implementation in
`src/solvers/smt2/smt2_parser.cpp::binary_predicate` rewrites
   (= (ite c A B) X)        ↦ (ite c (= A X[c]) (= B X))
   (distinct (ite c A B) X) ↦ (ite c (distinct A X[c]) (distinct B X))
   (le (ite c A B) X)       ↦ (ite c (le A X[c]) (le B X))
   ...
where `X[c]` denotes `X` with the equalities entailed by the
condition `c` substituted (`apply_cond_eq_substitution`). Each of
these rewrites is sound by case analysis on `c`.

We mechanise the soundness facts at the level of an arbitrary
type with a binary relation, so they apply uniformly to equality,
disequality, and the unsigned/signed relational predicates over
ZMod (2^d).
-/

import Mathlib.Tactic

namespace IteCondPropagation

variable {α β : Type*}

/-- Pushing a binary predicate through an ite at the left:
    `R (ite c A B) X = ite c (R A X) (R B X)`.

    Used to mechanise the parse-time rewrites
    `(= (ite c A B) X) ↦ (ite c (= A X) (= B X))`
    `(distinct (ite c A B) X) ↦ (ite c (distinct A X) (distinct B X))`
    `(le (ite c A B) X) ↦ (ite c (le A X) (le B X))`
    and analogous variants for lt, ge, gt. Sound for any binary
    predicate `R` regardless of how it relates to the values. -/
theorem predicate_through_ite_left
    (R : α → α → β) (c : Prop) [Decidable c] (A B X : α) :
    R (if c then A else B) X = if c then R A X else R B X := by
  by_cases h : c <;> simp [h]

/-- Pushing a binary predicate through an ite at the right:
    `R X (ite c A B) = ite c (R X A) (R X B)`. -/
theorem predicate_through_ite_right
    (R : α → α → β) (c : Prop) [Decidable c] (A B X : α) :
    R X (if c then A else B) = if c then R X A else R X B := by
  by_cases h : c <;> simp [h]

/-- If-condition propagation in the true branch: when the
    condition `c` entails an equality `x = v`, every occurrence of
    `x` in the true branch can be replaced by `v` without changing
    the value of the ite.

    Stated for the special case where `c` is the equality `x = v`
    itself; the substitution then trivially preserves the ite's
    value. -/
theorem if_cond_propagation
    {α : Type*} [DecidableEq α] {x v : α} (T F : α → α) :
    (if x = v then T x else F x) = if x = v then T v else F x := by
  by_cases h : x = v
  · simp [h]
  · simp [h]

/-- Specialised forms of `predicate_through_ite_left` for the
    parse-time rewrites in `binary_predicate`. -/

theorem eq_through_ite_left
    {α : Type*} [DecidableEq α] (c : Prop) [Decidable c] (A B X : α) :
    ((if c then A else B) = X) ↔ (if c then A = X else B = X) := by
  by_cases h : c <;> simp [h]

theorem notequal_through_ite_left
    {α : Type*} [DecidableEq α] (c : Prop) [Decidable c] (A B X : α) :
    ((if c then A else B) ≠ X) ↔ (if c then A ≠ X else B ≠ X) := by
  by_cases h : c <;> simp [h]

theorem le_through_ite_left
    {α : Type*} [LE α] [DecidableLE α]
    (c : Prop) [Decidable c] (A B X : α) :
    ((if c then A else B) ≤ X) ↔ (if c then A ≤ X else B ≤ X) := by
  by_cases h : c <;> simp [h]

theorem lt_through_ite_left
    {α : Type*} [LT α] [DecidableLT α]
    (c : Prop) [Decidable c] (A B X : α) :
    ((if c then A else B) < X) ↔ (if c then A < X else B < X) := by
  by_cases h : c <;> simp [h]

end IteCondPropagation
