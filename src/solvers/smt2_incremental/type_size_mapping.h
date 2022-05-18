// Author: Diffblue Ltd.

/// \file
/// Utilities for making a map of types to associated sizes.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_TYPE_SIZE_MAPPING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_TYPE_SIZE_MAPPING_H

#include <util/expr.h>

#include <solvers/smt2_incremental/object_tracking.h>
#include <solvers/smt2_incremental/smt_object_size.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <unordered_map>

using type_size_mapt = std::unordered_map<typet, smt_termt, irep_full_hash>;

/// This function populates the (pointer) type -> size map.
/// \param expression: the expression we're building the map for.
/// \param ns:
///   A namespace - passed to size_of_expr to lookup type symbols in case the
///   pointers have type `tag_typet`, rather than a more completely defined
///   type.
/// \param type_size_map:
///   A map of types to terms expressing the size of the type (in bytes). This
///   function adds new entries to the map for instances of pointer.base_type()
///   from \p expression which are not already keys in the map.
/// \param object_map: passed through to convert_expr_to_smt
/// \param object_size: passed through to convert_expr_to_smt
void associate_pointer_sizes(
  const exprt &expression,
  const namespacet &ns,
  type_size_mapt &type_size_map,
  const smt_object_mapt &object_map,
  const smt_object_sizet::make_applicationt &object_size);

#endif
