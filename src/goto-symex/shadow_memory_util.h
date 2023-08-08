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

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H
