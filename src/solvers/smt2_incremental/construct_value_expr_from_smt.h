// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_CONSTRUCT_VALUE_EXPR_FROM_SMT_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_CONSTRUCT_VALUE_EXPR_FROM_SMT_H

#include <util/expr.h>

#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/object_tracking.h>

class typet;

/// Mapping from a CBMC expression to the SMT identifier that has been
/// substituted for it during SMT conversion (e.g., a string constant whose
/// contents have been encoded as an array-typed SMT function). Used by
/// \ref construct_value_expr_from_smt to reverse the substitution and recover
/// the original expression for symbolic display in counterexample traces.
using smt_expression_identifier_mapt =
  std::unordered_map<exprt, smt_identifier_termt, irep_hash>;

/// \brief Given a \p value_term and a \p type_to_construct, this function
///   constructs an exprt that has the same value as the value term and the
///   same type as type to construct.
/// \details The construction works for bool and bitvector based types
///   including pointers. The bitvector based types use a bit level encoding
///   for their values which need decoding to be returned as a usable expt.
///   The compatibility of the type and value sort should be checked before
///   calling this function. Calling this function with mismatched type and
///   value will result in an invariant violation.
/// \param value_term
///   The value which the returned expr should have.
/// \param type_to_construct
///   The type which the constructed expr returned is expected to have.
/// \param ns
///   The namespace for type lookups.
exprt construct_value_expr_from_smt(
  const smt_termt &value_term,
  const typet &type_to_construct,
  const namespacet &ns);

/// \brief Overload that accepts an \p object_map and (optionally empty)
///   \p expression_identifiers for constructing annotated pointer constants.
///
/// When the type to construct is a pointer type, the \p object_map is used to
/// reconstruct a symbolic pointer expression from the encoded object ID and
/// offset in the bit-vector value. When the object's base expression is a
/// `symbol_exprt` introduced by identifier substitution (e.g., for string
/// constants), \p expression_identifiers is used to reverse that substitution
/// so the original expression appears in traces.
///
/// \param value_term
///   The SMT term encoding the value.
/// \param type_to_construct
///   The type which the constructed expr returned is expected to have.
/// \param ns
///   The namespace for type lookups.
/// \param object_map
///   Map from base expressions to tracked object information, used to
///   reconstruct symbolic pointer expressions for trace display.
/// \param expression_identifiers
///   Map from original expressions to their SMT identifier terms, as used
///   during expression-to-SMT conversion. Pass an empty map if no
///   substitution lookup is required.
exprt construct_value_expr_from_smt(
  const smt_termt &value_term,
  const typet &type_to_construct,
  const namespacet &ns,
  const smt_object_mapt &object_map,
  const smt_expression_identifier_mapt &expression_identifiers);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_CONSTRUCT_VALUE_EXPR_FROM_SMT_H
