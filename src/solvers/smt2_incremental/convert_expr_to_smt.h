// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H

#include <solvers/smt2_incremental/ast/smt_sorts.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/object_tracking.h>
#include <solvers/smt2_incremental/smt_is_dynamic_object.h>
#include <solvers/smt2_incremental/smt_object_size.h>
#include <solvers/smt2_incremental/type_size_mapping.h>

class exprt;
class typet;

/// \brief Converts the \p type to an smt encoding of the same expression
///   stored as sort ast (abstract syntax tree).
smt_sortt convert_type_to_smt_sort(const typet &type);

/// \brief Lower the `address_of(array[idx])` sub expressions in \p expr to
///   `idx + address_of(array)`, so that it can be fed to
///   `convert_expr_to_smt`.
exprt lower_address_of_array_index(exprt expr);

/// \brief Converts the \p expression to an smt encoding of the same expression
///   stored as term ast (abstract syntax tree).
smt_termt convert_expr_to_smt(
  const exprt &expression,
  const smt_object_mapt &object_map,
  const type_size_mapt &pointer_sizes,
  const smt_object_sizet::make_applicationt &object_size,
  const smt_is_dynamic_objectt::make_applicationt &is_dynamic_object);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H
