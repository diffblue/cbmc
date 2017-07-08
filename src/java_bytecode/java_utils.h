/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <util/type.h>
#include <util/symbol_table.h>

#include "java_bytecode_parse_tree.h"

#ifndef CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
#define CPROVER_JAVA_BYTECODE_JAVA_UTILS_H

bool java_is_array_type(const typet &type);

void generate_class_stub(
  const irep_idt &class_name,
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

/// Returns the number of JVM local variables (slots) taken by a local variable
/// that, when translated to goto, has type \p t.
unsigned java_local_variable_slots(const typet &t);

/// Returns the the number of JVM local variables (slots) used by the JVM to
/// pass, upon call, the arguments of a Java method whose type is \p t.
unsigned java_method_parameter_slots(const code_typet &t);

const std::string java_class_to_package(const std::string &canonical_classname);

/// Attaches a source location to an expression and all of its subexpressions.
/// Usually only codet needs this, but there are a few known examples of
/// expressions needing a location, such as
/// `goto_convertt::do_function_call_symbol` (function() needs a location)
/// and `goto_convertt::clean_expr` (any subexpression being split into a
/// separate instruction needs a location), so for safety we give every
/// mentioned expression a location.
/// Any code or expressions with source location fields already set keep those
/// fields using rules of source_locationt::merge.
void merge_source_location_rec(
  exprt &expr,
  const source_locationt &source_location);

#endif // CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
