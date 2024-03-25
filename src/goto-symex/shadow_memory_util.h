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

#include "goto_symex_state.h" // IWYU pragma: keep

// To enable logging of Shadow Memory functions define DEBUG_SHADOW_MEMORY

class exprt;
class typet;

/// Logs setting a value to a given shadow field. Mainly for use for
/// debugging purposes.
void shadow_memory_log_set_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr,
  const exprt &value);

/// Logs the retrieval of the value associated with a given shadow
/// memory field. Mainly for use for debugging purposes. Dual to
/// shadow_memory_log_get_field.
void shadow_memory_log_value_set(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set);

/// Logs getting a value corresponding to a shadow memory field. Mainly used for
/// debugging purposes.
void shadow_memory_log_get_field(
  const namespacet &ns,
  const messaget &log,
  const irep_idt &field_name,
  const exprt &expr);

/// Logs a successful match between an address and a value within the value set.
void shadow_memory_log_value_set_match(
  const namespacet &ns,
  const messaget &log,
  const exprt &address,
  const exprt &expr);

/// Generic logging function that will log depending on the configured
/// verbosity. The log will be a specific message given to it, along with an
/// expression passed along to it.
void shadow_memory_log_text_and_expr(
  const namespacet &ns,
  const messaget &log,
  const char *text,
  const exprt &expr);

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
void clean_pointer_expr(exprt &expr);

/// Wraps a given expression into a `dereference_exprt` unless it is an
/// `address_of_exprt` in which case it just unboxes it and returns its content.
exprt deref_expr(const exprt &expr);

/// Replace an invalid object by a null pointer. Works recursively on the
/// operands (child nodes) of the expression, as well.
/// \param expr The (root) expression where substitution will happen.
void replace_invalid_object_by_null(exprt &expr);

/// Retrieve the expression that a field was initialised with within a given
/// symex state.
/// \param field_name The field whose initialisation expression we want to
///   retrieve.
/// \param state The goto symex state within which we want to search for the
///   expression.
/// \returns The expression the field was initialised with.
const exprt &
get_field_init_expr(const irep_idt &field_name, const goto_symex_statet &state);

/// Get a list of `(condition, value)` pairs for a certain pointer from
/// the shadow memory, where each pair denotes the `value` of the pointer
/// expression if the `condition` evaluates to `true`.
/// \return A vector of pair<expr, expr> corresponding to a condition and value.
///    (See above for explanation).
std::vector<std::pair<exprt, exprt>> get_shadow_dereference_candidates(
  const namespacet &ns,
  const messaget &log,
  const exprt &matched_object,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const typet &field_type,
  const exprt &expr,
  const typet &lhs_type,
  bool &exact_match);

/// Retrieves the type of the shadow memory by returning the type of the shadow
/// memory initializer value.
/// \param field_name The name of the field whose value type we want to query.
/// \param state The symex_state within which the query is executed (the field's
///    value is looked up).
/// \returns The type of the value the field was initialised with (actually,
///    the type of the value the field currently is associated with, but it's
///    invariant since the declaration).
const typet &
get_field_init_type(const irep_idt &field_name, const goto_symex_statet &state);

/// Given a pointer expression check to see if it can be a null pointer or an
/// invalid object within value_set.
/// \param address A pointer expressions that we are using as the query.
/// \param value_set The search space for the query.
/// \returns true if the object can be null or invalid in the value set, false
///    otherwise.
bool contains_null_or_invalid(
  const std::vector<exprt> &value_set,
  const exprt &address);

/// Performs aggregation of the shadow memory field value over multiple bytes
/// for fields whose type is _Bool.
/// \param expr the type to compute the or over each of its bytes
/// \param field_type the type of the shadow memory (must be `c_bool` or `bool`)
/// \param ns the namespace within which we're going to perform symbol lookups
/// \param log the message log to which we're going to print debugging messages,
///   if debugging is set
/// \param is_union `true` if the expression expr is part of a union.
/// \return the aggregated `or` byte-sized value contained in expr
exprt compute_or_over_bytes(
  const exprt &expr,
  const typet &field_type,
  const namespacet &ns,
  const messaget &log,
  const bool is_union);

/// Performs aggregation of the shadow memory field value over multiple cells
/// for fields whose type is a signed/unsigned bitvector (where the value is
/// arbitrary up until the max represented by the bitvector size).
/// \param expr the expression to extract the max from
/// \param field_type the type of the shadow memory field to return
/// \param ns the namespace to perform type-lookups into
/// \return the aggregated max byte-sized value contained in expr
/// Note that the expr type size must be known at compile time.
exprt compute_max_over_bytes(
  const exprt &expr,
  const typet &field_type,
  const namespacet &ns);

/// Build an if-then-else chain from a vector containing pairs of expressions.
/// \param conds_values Contains pairs <e1, e2>, where `e1` is going to be
///    used as an antecedent for an if_expr, and `e2` is going to be used
///    as the consequent.
/// \returns An if_exprt of the form `if e1 then e2 else if e3 then e4 else ...`
/// \note the expression created will not have the first condition as the first
///    element will serve fallback if all the other conditions are `false`.
exprt build_if_else_expr(
  const std::vector<std::pair<exprt, exprt>> &conds_values);

/// Checks if value_set contains only a `NULL` pointer expression of the same
///   type of expr.
/// \param ns the namespace within which we're going to perform symbol lookups
/// \param log the message log to which we're going to print debugging messages,
///   if debugging is set
/// \param value_set the collection to check if it contains *only* the `NULL`
///   pointer
/// \param expr a pointer-typed expression
/// \return `true` if value_set contains only a `NULL` pointer expression
bool check_value_set_contains_only_null_ptr(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set,
  const exprt &expr);

/// Get shadow memory values for a given expression within a specified value
/// set.
/// \returns if potential values are present for that object inside the value
///    set, then we get back an `if e1 then e2 else (if e3 else e4...`
///    expression, where `e1`, `e3`, ... are guards (conditions) and `e2`, `e4`,
///    etc are the possible values of the object within the value set.
std::optional<exprt> get_shadow_memory(
  const exprt &expr,
  const std::vector<exprt> &value_set,
  const std::vector<shadow_memory_statet::shadowed_addresst> &addresses,
  const namespacet &ns,
  const messaget &log,
  size_t &mux_size);

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H
