/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation Utilities

#ifndef CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H
#define CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H

#include <util/irep.h>
#include <util/message.h> // IWYU pragma: keep

#include <pointer-analysis/value_set_dereference.h>

#include "goto_symex_state.h" // IWYU pragma: keep

class exprt;
class typet;

/// Extracts the field name identifier from a string expression,
/// e.g. as passed as argument to a __CPROVER_field_decl_local call.
/// \param string_expr The string argument expression
/// \return The identifier denoted by the string argument expression
irep_idt extract_field_name(const exprt &string_expr);

/// Clean the given pointer expression so that it has the right
/// shape for being used for identifying shadow memory.
/// This handles some quirks regarding array sizes containing
/// L2 symbols and string constants not having char-pointer type.
/// \param expr The pointer to the original memory, e.g. as passed to
///    __CPROVER_field_get.
/// \param type The followed type of expr.
void clean_pointer_expr(exprt &expr, const typet &type);

// TODO: Daxygen
exprt deref_expr(const exprt &expr);

// TODO: DOxYGEN
void log_set_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr,
  const exprt &value);

// TODO: doxygen
void log_get_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr);

// TODO: doxygen
void log_value_set(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set);

// TODO: doxygen
void log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const shadow_memory_statet::shadowed_addresst &shadowed_address,
  const exprt &matched_base_address,
  const value_set_dereferencet::valuet &dereference,
  const exprt &expr,
  const value_set_dereferencet::valuet &shadow_dereference);

// TODO: doxygen
void log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const exprt &address,
  const exprt &expr);

// TODO: doxygen
void log_try_shadow_address(
  const namespacet &ns,
  const messaget &log,
  const shadow_memory_statet::shadowed_addresst &shadowed_address);

// TODO: doxygen
void log_cond(
  const namespacet &ns,
  const messaget &log,
  const char *cond_text,
  const exprt &cond);

// TODO: doxygen
void replace_invalid_object_by_null(exprt &expr);

// TODO: doxygen
const exprt &
get_field_init_expr(const irep_idt &field_name, const goto_symex_statet &state);

// TODO: doxygen?
std::vector<std::pair<exprt, exprt>> get_shadow_dereference_candidates(
  const namespacet &ns,
  const messaget &log,
  const exprt &matched_object,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const typet &field_type,
  const exprt &expr,
  const typet &lhs_type,
  bool &exact_match);

// TODO: doxygen
bool contains_null_or_invalid(
  const std::vector<exprt> &value_set,
  const exprt &address);

// TODO: doxygen
exprt compute_or_over_cells(
  const exprt &expr,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union);

// TODO: doxygen
exprt compute_max_over_cells(
  const exprt &expr,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union);

// TODO: doxygen?
exprt build_if_else_expr(
  const std::vector<std::pair<exprt, exprt>> &conds_values);

// TODO: improve?
/// returns true if we attempt to set/get a field on a NULL pointer
bool set_field_check_null(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set,
  const exprt &expr);

// TODO: improve?
/// Used for set_field and shadow memory copy
optionalt<exprt> get_shadow_memory(
  const exprt &expr,
  const std::vector<exprt> &value_set,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const namespacet &ns,
  const messaget &log,
  size_t &mux_size);

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H
