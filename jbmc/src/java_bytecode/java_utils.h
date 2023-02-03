/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
#define CPROVER_JAVA_BYTECODE_JAVA_UTILS_H

#include <unordered_set>

#include <util/nodiscard.h>
#include <util/pointer_expr.h>

#include <goto-programs/resolve_inherited_component.h>

class java_class_typet;
class java_method_typet;
class message_handlert;
class symbol_table_baset;

/// Returns true iff the argument represents a string type (CharSequence,
/// StringBuilder, StringBuffer or String).
/// The check for the length and data components is necessary in the case where
/// string refinement is not activated. In this case, \p struct_type only
/// contains the standard Object fields (or may have some other model entirely),
/// and in particular may not have length and data fields.
bool is_java_string_type(const struct_typet &struct_type);

/// Return type for get_java_primitive_type_info
struct java_primitive_type_infot
{
  /// Name, including java:: prefix, of the corresponding boxed type
  const irep_idt boxed_type_name;
  /// Full identifier of the boxed type's factory method that takes the
  /// corresponding primitive as its sole argument
  const irep_idt boxed_type_factory_method;
  /// Full identifier of the most general boxed-type method that yields this
  /// type. For most primitives that means the corresponding method on
  /// java.lang.Number; for Character and Boolean it means the method on their
  /// specific boxed type.
  const irep_idt unboxing_function_name;
};

/// If \p primitive_type is a Java primitive type, return information about it,
/// otherwise return null
const java_primitive_type_infot *
get_java_primitive_type_info(const typet &maybe_primitive_type);

/// Return type for get_boxed_type_info_by_name
struct java_boxed_type_infot
{
  /// Name of the function defined on the boxed type that returns the boxed
  /// value
  const irep_idt unboxing_function_name;
  /// Primitive type that this boxed type contains
  const typet corresponding_primitive_type;
};

/// If \p type_name is a Java boxed type tag, return information about it,
/// otherwise return null
const java_boxed_type_infot *
get_boxed_type_info_by_name(const irep_idt &type_name);

/// Returns true iff the argument is the symbol-table identifier of a Java
/// primitive wrapper type (for example, java::java.lang.Byte)
bool is_primitive_wrapper_type_id(const irep_idt &id);

/// Returns true iff the argument is the fully qualified name of a Java
/// primitive wrapper type (for example, java.lang.Byte)
bool is_primitive_wrapper_type_name(const std::string &type_name);

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

/// Given a pointer type to a Java class and a type representing a more specific
/// Java class, return a pointer type to the more specific class with the same
/// structure as the original pointer type.
pointer_typet pointer_to_replacement_type(
  const pointer_typet &given_pointer_type,
  const java_class_typet &replacement_class_type);

/// Dereference an expression and flag it for a null-pointer check
/// \param expr: expression to dereference and check
dereference_exprt checked_dereference(const exprt &expr);

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

exprt make_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &range,
  symbol_table_baset &symbol_table);

irep_idt strip_java_namespace_prefix(const irep_idt &to_strip);

std::string pretty_print_java_type(const std::string &fqn_java_type);

optionalt<resolve_inherited_componentt::inherited_componentt>
get_inherited_component(
  const irep_idt &component_class_id,
  const irep_idt &component_name,
  const symbol_table_baset &symbol_table,
  bool include_interfaces);

bool is_non_null_library_global(const irep_idt &);

extern const std::unordered_set<std::string> cprover_methods_to_ignore;

symbolt &fresh_java_symbol(
  const typet &type,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &function_name,
  symbol_table_baset &symbol_table);

/// Gets the identifier of the class which declared a given \p symbol. If the
/// symbol is not declared by a class then an empty optional is returned. This
/// is used for method symbols and static field symbols to link them back to the
/// class which declared them.
optionalt<irep_idt> declaring_class(const symbolt &symbol);

/// Sets the identifier of the class which declared a given \p symbol to \p
/// declaring_class.
void set_declaring_class(symbolt &symbol, const irep_idt &declaring_class);

/// Get JVM type name of the class in which \p method_name is defined.
/// Returns an empty optional if the class name cannot be retrieved,
/// e.g. method_name is an internal function.
NODISCARD optionalt<std::string>
class_name_from_method_name(const std::string &method_name);

#endif // CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
