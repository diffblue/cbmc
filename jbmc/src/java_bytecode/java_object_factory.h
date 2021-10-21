/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// This module is responsible for the synthesis of code (in the form of a
/// sequence of codet statements) that can allocate and initialize
/// non-deterministically both primitive Java types and objects. The
/// non-deterministic initialization of one object triggers the
/// non-deterministic initialization of all its fields, which in turn could be
/// references to other objects. We thus speak about an object tree.
///
/// This is useful for, e.g., the creation of a verification harness (non-det
/// initialization of the parameters of the method to verify), mocking methods
/// that are called but for which we don't have a body (overapproximating the
/// return value and possibly side effects).
///
/// The two main APIs are \ref gen_nondet_init() and \ref object_factory()
/// (which calls gen_nondet_init()), at the bottom of the file.
/// A call to
///
///   gen_nondet_init(expr, code, ..., update_in_place)
///
/// appends to `code` (a code_blockt) a sequence of statements that
/// non-deterministically initialize the `expr` (which is expected to be an
/// l-value exprt) with a primitive or reference value of type equal to or
/// compatible with `expr.type()` -- see documentation for the argument
/// `pointer_type_selector` for additional details. gen_nondet_init() is the
/// starting point of a recursive algorithm, and most other functions in this
/// file are different (recursive or base) cases depending on the type of expr.
///
/// The code generated mainly depends on the parameter `update_in_place`. Assume
/// that `expr` is a reference to an object (in our IR, that means a pointer to
/// a struct).
///
/// When update_in_place == NO_UPDATE_IN_PLACE, the following code is
/// generated:
///
/// ```
///     struct MyClass object;
///     if (NONDET(bool))
///       expr = NULL;
///     else
///       expr = &object;
///       ... // non-det initialization of `object` in NO_UPDATE_IN_PLACE mode
/// ```
///
/// When update_in_place == MUST_UPDATE_IN_PLACE, the following code is
/// generated (assuming that MyClass has fields "int x" and "OtherClass y"):
///
/// ```
///     expr->x = NONDET(int);
///     expr->y = ... // non-det initialization in MUST_UPDATE_IN_PLACE mode
/// ```
///
/// When update_in_place == MAY_UPDATE_IN_PLACE, the following code is
/// generated:
///
/// ```
///     if (NONDET(bool))
///       ... // non-det initialization of `expr` in MUST_UPDATE_IN_PLACE
///     else
///       ... // non-det initialization of `expr` in NO_UPDATE_IN_PLACE
/// ```
///

#ifndef CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H
#define CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H

#include "nondet.h"

#include <goto-programs/allocate_objects.h>

#include <util/std_code.h>

class message_handlert;
class select_pointer_typet;
class symbol_tablet;
struct java_object_factory_parameterst;

exprt object_factory(
  const typet &type,
  const irep_idt base_name,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  java_object_factory_parameterst parameters,
  lifetimet lifetime,
  const source_locationt &location,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &log);

exprt object_factory(
  const typet &type,
  const irep_idt base_name,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const java_object_factory_parameterst &object_factory_parameters,
  lifetimet lifetime,
  const source_locationt &location,
  message_handlert &log);

enum class update_in_placet
{
  NO_UPDATE_IN_PLACE,
  MAY_UPDATE_IN_PLACE,
  MUST_UPDATE_IN_PLACE
};

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  bool skip_classid,
  lifetimet lifetime,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  update_in_placet update_in_place,
  message_handlert &log);

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  bool skip_classid,
  lifetimet lifetime,
  const java_object_factory_parameterst &object_factory_parameters,
  update_in_placet update_in_place,
  message_handlert &log);

using array_element_generatort = std::function<
  code_blockt(const exprt &element_at_counter, const typet &element_type)>;

/// Synthesize GOTO for generating a array of nondet length to be stored in the
/// \p expr.
/// \param expr: The array expression to initialize.
/// \param update_in_place: Should the code allow the solver the freedom to
/// leave the array as is.
/// \param location: Source location to use for all synthesized code.
/// \param element_generator: A function that creates a new element and assigns
/// it to the provided expression.
/// \param allocate_local_symbol: A function that creates a local symbol in the
/// symbol table. See \ref java_object_factoryt::assign_element for an example
/// implementation.
/// \param symbol_table: The symbol table.
/// \param max_nondet_array_length: The maximum size the array can be.
/// \return The GOTO that approximates:
/// ```
/// array_length = NONDET(int)
/// ASSUME(array_length < max_nondet_array_length)
/// expr = java_new_array(max_nondet_array_length)
/// expr->length = array_length
/// for (int i = 0; i < array_length; ++i)
///   `element_generator()`
/// ```
code_blockt gen_nondet_array_init(
  const exprt &expr,
  update_in_placet update_in_place,
  const source_locationt &location,
  const array_element_generatort &element_generator,
  const allocate_local_symbolt &allocate_local_symbol,
  const symbol_tablet &symbol_table,
  size_t max_nondet_array_length);

#endif // CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H
