/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
#define CPROVER_JAVA_BYTECODE_JAVA_UTILS_H

#include "java_types.h"

#include <unordered_set>

#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/resolve_inherited_component.h>

bool java_is_array_type(const typet &type);

void generate_class_stub(
  const irep_idt &class_name,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const struct_union_typet::componentst &componentst);

/// Returns the number of JVM local variables (slots) taken by a local variable
/// that, when translated to goto, has type \p t.
unsigned java_local_variable_slots(const typet &t);

/// Returns the the number of JVM local variables (slots) used by the JVM to
/// pass, upon call, the arguments of a Java method whose type is \p t.
unsigned java_method_parameter_slots(const java_method_typet &t);

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

#define JAVA_STRING_LITERAL_PREFIX "java::java.lang.String.Literal"

/// \param id: any string
/// \return Returns true if 'id' identifies a string literal symbol
bool is_java_string_literal_id(const irep_idt &id);

/// Resolves a user-friendly method name (like packagename.Class.method)
/// into an internal name (like java::packagename.Class.method:()V)
/// The input may also have a type descriptor suffix to resolve ambiguity.
/// On error, returns irep_idt() and sets error.
/// \param friendly_name: user-friendly method name
/// \param symbol_table: global symbol table
/// \param [out] error: gets error description on failure
irep_idt resolve_friendly_method_name(
  const std::string &friendly_name,
  const symbol_table_baset &symbol_table,
  std::string &error);

/// Dereference an expression and flag it for a null-pointer check
/// \param expr: expression to dereference and check
/// \param type: expected result type (typically expr.type().subtype())
dereference_exprt checked_dereference(const exprt &expr, const typet &type);

/// Add the components in components_to_add to the class denoted
/// by class symbol.
/// \param class_symbol: The symbol representing the class we want to modify.
/// \param components_to_add: The vector with the components we want to add.
void java_add_components_to_class(
  symbolt &class_symbol,
  const struct_union_typet::componentst &components_to_add);

size_t find_closing_delimiter(
  const std::string &src,
  size_t position,
  char open_char,
  char close_char);

void declare_function(
  irep_idt function_name,
  const typet &type,
  symbol_table_baset &symbol_table);

exprt make_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &type,
  symbol_table_baset &symbol_table);

irep_idt strip_java_namespace_prefix(const irep_idt &to_strip);

std::string pretty_print_java_type(const std::string &fqn_java_type);

resolve_inherited_componentt::inherited_componentt get_inherited_component(
  const irep_idt &component_class_id,
  const irep_idt &component_name,
  const symbol_tablet &symbol_table,
  const class_hierarchyt &class_hierarchy,
  bool include_interfaces);

bool is_non_null_library_global(const irep_idt &);

extern const std::unordered_set<std::string> cprover_methods_to_ignore;

#endif // CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
