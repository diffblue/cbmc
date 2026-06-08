/// \file
/// Tseitin-aware boolean propagation for the algebraic solver.
///
/// Industrial bv-encodings (e.g., Wienand-style data-path
/// equivalence checks) often wrap polynomial equalities in chains
/// of Tseitin-style boolean variables:
/// \code
///   (= Fresh__0 (= var16 var28))    ; Fresh__0 ↔ (var16 = var28)
///   (= var29 Fresh__0)
///   (= var30 (bvnot 1))             ; var30 := 0 (constant)
///   (= var31 (bvor var29 var30))    ; var31 := var29 ∨ 0 = var29
///   (= property (extract 0 0 var31)); property := var31[0]
///   (= Fresh__1 (= property 0))     ; Fresh__1 ↔ (property = 0)
///   (= 1 Fresh__1)                  ; assert Fresh__1
/// \endcode
///
/// Without preprocessing, the algebraic solver does not see the
/// underlying disequality `var16 ≠ var28` because it is buried
/// inside the Tseitin chain. The polynomial commutativity proof
/// (var16 = var28 by ring axioms) is invisible.
///
/// `tseitin_propagatort` builds a definitions map from the
/// asserted `(= bool_sym X)` equalities and a known-value map
/// from the asserted `(= bool_sym constant)` equalities, then
/// runs forward simplification + backward inversion to a fixed
/// point. When backward inversion of a known boolean variable's
/// definition produces a non-trivial bit-vector equality, that
/// equality is emitted as a polynomial dis/equality.
///
/// Soundness: each backward inversion step is sound by the
/// classical rule (e.g., `bvor a b = 0 ⟹ a = 0 ∧ b = 0`,
/// `bvnot a = v ⟹ a = ¬v`, `(= a b) = 0 ⟹ a ≠ b`); the rules
/// are mechanised in `formal-proofs/TseitinPropagation.lean`.

#ifndef CPROVER_SOLVERS_FLATTENING_TSEITIN_PROPAGATION_H
#define CPROVER_SOLVERS_FLATTENING_TSEITIN_PROPAGATION_H

#include <util/expr.h>
#include <util/mp_arith.h>
#include <util/std_expr.h>

#include <unordered_map>
#include <vector>

/// Discovers polynomial dis/equalities buried in Tseitin-style
/// boolean chains. See file-level comment for motivation and
/// soundness argument. PROOF: formal-proofs/TseitinPropagation.lean
class tseitin_propagatort
{
public:
  /// Collect Tseitin-style boolean chains from `equalities`.
  /// Each entry is interpreted as `(= a b)` set to true (i.e., a
  /// SSA-style definition or a value assertion). Run propagation
  /// to a fixed point; results are available via `equalities()`
  /// / `disequalities()` afterwards.
  void run(const std::vector<exprt> &equalities);

  /// Polynomial bit-vector equalities discovered by backward
  /// inversion (corresponding to a Tseitin chain that fixes
  /// some bool_sym to 1, where the sym's definition is a
  /// bit-vector equality).
  const std::vector<equal_exprt> &equalities() const
  {
    return implied_equalities;
  }

  /// Polynomial bit-vector disequalities discovered by backward
  /// inversion (sym fixed to 0, definition is a bit-vector
  /// equality).
  const std::vector<equal_exprt> &disequalities() const
  {
    return implied_disequalities;
  }

private:
  /// Map from boolean-symbol identifier to its definition
  /// expression (the right-hand side of an asserted
  /// `(= bool_sym def_expr)`).
  std::unordered_map<irep_idt, exprt, irep_id_hash> defs;

  /// Map from boolean-symbol identifier to its known constant
  /// value (0 or 1), populated by forward simplification and
  /// backward inversion.
  std::unordered_map<irep_idt, mp_integer, irep_id_hash> known;

  /// Has the propagator detected a contradiction (e.g., a sym
  /// forced to two different values)? If so, the formula is
  /// trivially UNSAT.
  bool contradiction = false;

  std::vector<equal_exprt> implied_equalities;
  std::vector<equal_exprt> implied_disequalities;

  /// Ingest one `(= a b)` equality: add to `defs` if it has the
  /// shape `(bool_sym, expr)`, add to `known` if it has the
  /// shape `(bool_sym, constant)`.
  void ingest(const equal_exprt &eq);

  /// Try to evaluate `e` to a constant given the current
  /// `known` map (forward simplification).
  std::optional<mp_integer> evaluate(const exprt &e);

  /// Backward propagation: `e` is constrained to evaluate to
  /// `value`. Recursively infer constraints on subexpressions.
  /// May add to `known`, emit `implied_equalities`, emit
  /// `implied_disequalities`, or set `contradiction`.
  void enforce(const exprt &e, const mp_integer &value);

  /// Run forward simplification + backward inversion to a fixed
  /// point.
  void propagate();

  /// Helpers.
  static bool is_bool_typed(const typet &t);

public:
  /// Same as `is_bool_typed` (public for use by free helper functions
  /// in the implementation file).
  static bool is_bool_typed_static(const typet &t)
  {
    return is_bool_typed(t);
  }

private:
  static std::optional<mp_integer> as_const(const exprt &e);
};

#endif // CPROVER_SOLVERS_FLATTENING_TSEITIN_PROPAGATION_H
