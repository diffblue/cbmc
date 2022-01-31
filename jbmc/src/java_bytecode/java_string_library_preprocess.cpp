/*******************************************************************\

Module: Java_string_libraries_preprocess, gives code for methods on
        strings of the java standard library. In particular methods
        from java.lang.String, java.lang.StringBuilder,
        java.lang.StringBuffer.

Author: Romain Brenguier

Date:   April 2017

\*******************************************************************/

/// \file
/// Java_string_libraries_preprocess, gives code for methods on strings of the
///   java standard library. In particular methods from java.lang.String,
///   java.lang.StringBuilder, java.lang.StringBuffer.

#include <goto-programs/allocate_objects.h>
#include <goto-programs/class_identifier.h>

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/floatbv_expr.h>
#include <util/refined_string_type.h>
#include <util/std_code.h>
#include <util/string_expr.h>

#include "java_types.h"
#include "java_utils.h"

#include "java_string_library_preprocess.h"

/// \return tag of a struct prefixed by "java::" or symbolic tag
///   empty string if not symbol or struct
static irep_idt get_tag(const typet &type)
{
  /// \todo Use follow instead of assuming tag to symbol relationship.
  if(type.id() == ID_struct_tag)
    return to_struct_tag_type(type).get_identifier();
  else if(type.id() == ID_struct)
    return irep_idt("java::" + id2string(to_struct_type(type).get_tag()));
  else
    return irep_idt();
}

/// \param type: a type
/// \param tag: a string
/// \return Boolean telling whether the type is a struct with the given tag or a
///   symbolic type with the tag prefixed by "java::"
bool java_string_library_preprocesst::java_type_matches_tag(
  const typet &type, const std::string &tag)
{
  return irep_idt("java::" + tag) == get_tag(type);
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java string pointer
bool java_string_library_preprocesst::is_java_string_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &base_type = pt.base_type();
    return is_java_string_type(base_type);
  }
  return false;
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java string
bool java_string_library_preprocesst::is_java_string_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.String");
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java StringBuilder
bool java_string_library_preprocesst::is_java_string_builder_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.StringBuilder");
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java StringBuilder
///   pointers
bool java_string_library_preprocesst::is_java_string_builder_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &base_type = pt.base_type();
    return is_java_string_builder_type(base_type);
  }
  return false;
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java StringBuffer
bool java_string_library_preprocesst::is_java_string_buffer_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.StringBuffer");
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java StringBuffer
///   pointers
bool java_string_library_preprocesst::is_java_string_buffer_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &base_type = pt.base_type();
    return is_java_string_buffer_type(base_type);
  }
  return false;
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java char sequence
bool java_string_library_preprocesst::is_java_char_sequence_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.CharSequence");
}

/// \param type: a type
/// \return Boolean telling whether the type is that of a pointer to a java char
///   sequence
bool java_string_library_preprocesst::is_java_char_sequence_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &base_type = pt.base_type();
    return is_java_char_sequence_type(base_type);
  }
  return false;
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java char array
bool java_string_library_preprocesst::is_java_char_array_type(
  const typet &type)
{
  return java_type_matches_tag(type, "array[char]");
}

/// \par parameters: a type
/// \return Boolean telling whether the type is that of a pointer to a java char
///   array
bool java_string_library_preprocesst::is_java_char_array_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &base_type = pt.base_type();
    return is_java_char_array_type(base_type);
  }
  return false;
}

/// \return the type of the length field in java Strings.
static typet string_length_type()
{
  return java_int_type();
}

/// Gets the base classes for known String and String-related types, or returns
/// an empty list for other types.
/// \param class_name: class identifier, without "java::" prefix.
/// \return a list of base classes, again without "java::" prefix.
std::vector<irep_idt>
java_string_library_preprocesst::get_string_type_base_classes(
  const irep_idt &class_name)
{
  if(!is_known_string_type(class_name))
    return {};

  std::vector<irep_idt> bases;
  bases.reserve(3);

  // StringBuilder and StringBuffer derive from AbstractStringBuilder;
  // other String types (String and CharSequence) derive directly from Object.
  if(
    class_name == "java.lang.StringBuilder" ||
    class_name == "java.lang.StringBuffer")
    bases.push_back("java.lang.AbstractStringBuilder");
  else
    bases.push_back("java.lang.Object");

  // Interfaces:
  if(class_name != "java.lang.CharSequence")
  {
    bases.push_back("java.io.Serializable");
    bases.push_back("java.lang.CharSequence");
  }
  if(class_name == "java.lang.String")
    bases.push_back("java.lang.Comparable");

  return bases;
}

/// Add to the symbol table type declaration for a String-like Java class.
/// \param class_name: a name for the class such as "java.lang.String"
/// \param symbol_table: symbol table to which the class will be added
void java_string_library_preprocesst::add_string_type(
  const irep_idt &class_name, symbol_tablet &symbol_table)
{
  irep_idt class_symbol_name = "java::" + id2string(class_name);
  symbolt tmp_string_symbol;
  tmp_string_symbol.name = class_symbol_name;
  symbolt *string_symbol = nullptr;
  bool already_exists = symbol_table.move(tmp_string_symbol, string_symbol);

  if(already_exists)
  {
    // A library has already defined this type -- we'll replace its
    // components with those required for internal string modelling, but
    // otherwise leave it alone.
    to_java_class_type(string_symbol->type).components().clear();
  }
  else
  {
    // No definition of this type exists -- define it as it usually occurs in
    // the JDK:
    java_class_typet new_string_type;
    new_string_type.set_tag(class_name);
    new_string_type.set_name(class_symbol_name);
    new_string_type.set_access(ID_public);

    std::vector<irep_idt> bases = get_string_type_base_classes(class_name);
    for(const irep_idt &base_name : bases)
      new_string_type.add_base(
        struct_tag_typet("java::" + id2string(base_name)));

    string_symbol->base_name = id2string(class_name);
    string_symbol->pretty_name = id2string(class_name);
    string_symbol->type = new_string_type;
    string_symbol->is_type = true;
    string_symbol->mode = ID_java;
  }

  auto &string_type = to_java_class_type(string_symbol->type);

  string_type.components().resize(3);
  const struct_tag_typet &supertype = string_type.bases().front().type();
  irep_idt supertype_component_name =
    "@" + id2string(supertype.get_identifier()).substr(6);
  string_type.components()[0].set_name(supertype_component_name);
  string_type.components()[0].set_pretty_name(supertype_component_name);
  string_type.components()[0].type() = supertype;
  string_type.components()[1].set_name("length");
  string_type.components()[1].set_pretty_name("length");
  string_type.components()[1].type()=string_length_type();
  string_type.components()[2].set_name("data");
  string_type.components()[2].set_pretty_name("data");
  string_type.components()[2].type() = pointer_type(java_char_type());
}

/// calls string_refine_preprocesst::process_operands with a list of parameters.
/// \param params: a list of function parameters
/// \param loc: location in the source
/// \param function_id: name of the function in which the code will be added
/// \param symbol_table: symbol table
/// \param init_code: code block, in which declaration of some arguments may be
///   added
/// \return a list of expressions
exprt::operandst java_string_library_preprocesst::process_parameters(
  const java_method_typet::parameterst &params,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : params)
    ops.emplace_back(symbol_exprt(p.get_identifier(), p.type()));
  return process_operands(ops, loc, function_id, symbol_table, init_code);
}

/// Creates a string_exprt from the input exprt representing a char sequence
/// \param expr_to_process: an expression of a type which implements char
///   sequence
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param function_id: name of the function in which the code will be added
/// \param init_code: code block, in which declaration will be added:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// char *cprover_string_content;
/// int cprover_string_length;
/// cprover_string_length = a->length;
/// cprover_string_content = a->data;
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// \return the processed operand:
///   {content=cprover_string_content, length=cprover_string_length}
refined_string_exprt
java_string_library_preprocesst::convert_exprt_to_string_exprt(
  const exprt &expr_to_process,
  const source_locationt &loc,
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  code_blockt &init_code)
{
  PRECONDITION(implements_java_char_sequence_pointer(expr_to_process.type()));
  const refined_string_exprt string_expr =
    decl_string_expr(loc, function_id, symbol_table, init_code);
  code_assign_java_string_to_string_expr(
    string_expr, expr_to_process, loc, symbol_table, init_code);
  return string_expr;
}

/// for each expression that is of a type implementing strings, we declare a new
/// `cprover_string` whose contents is deduced from the expression, replace
/// the expression by this cprover_string in the output list, and add an
/// assumption that the object is not null; in the other case
/// the expression is kept as is for the output list. Also does the same thing
/// for char array references.
/// \param operands: a list of expressions
/// \param loc: location in the source
/// \param function_id: name of the function in which the code will be added
/// \param symbol_table: symbol table
/// \param init_code: code block, in which declaration of some arguments may be
///   added
/// \return a list of expressions
exprt::operandst java_string_library_preprocesst::process_operands(
  const exprt::operandst &operands,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : operands)
  {
    if(implements_java_char_sequence_pointer(p.type()))
    {
      init_code.add(code_assumet(
        notequal_exprt(p, null_pointer_exprt(to_pointer_type(p.type())))));
      ops.push_back(convert_exprt_to_string_exprt(
        p, loc, symbol_table, function_id, init_code));
    }
    else if(is_java_char_array_pointer_type(p.type()))
      ops.push_back(
        replace_char_array(p, loc, function_id, symbol_table, init_code));
    else
      ops.push_back(p);
  }
  return ops;
}

/// Finds the type of the data component
/// \param type: a type containing a "data" component
/// \param symbol_table: symbol table
/// \return type of the "data" component
static const typet &
get_data_type(const typet &type, const symbol_tablet &symbol_table)
{
  PRECONDITION(type.id() == ID_struct || type.id() == ID_struct_tag);
  if(type.id() == ID_struct_tag)
  {
    const symbolt &sym =
      symbol_table.lookup_ref(to_struct_tag_type(type).get_identifier());
    CHECK_RETURN(sym.type.id() != ID_struct_tag);
    return get_data_type(sym.type, symbol_table);
  }
  // else type id is ID_struct
  const struct_typet &struct_type=to_struct_type(type);
  return struct_type.component_type("data");
}

/// Finds the type of the length component
/// \param type: a type containing a "length" component
/// \param symbol_table: symbol table
/// \return type of the "length" component
static const typet &
get_length_type(const typet &type, const symbol_tablet &symbol_table)
{
  PRECONDITION(type.id() == ID_struct || type.id() == ID_struct_tag);
  if(type.id() == ID_struct_tag)
  {
    const symbolt &sym =
      symbol_table.lookup_ref(to_struct_tag_type(type).get_identifier());
    CHECK_RETURN(sym.type.id() != ID_struct_tag);
    return get_length_type(sym.type, symbol_table);
  }
  // else type id is ID_struct
  const struct_typet &struct_type=to_struct_type(type);
  return struct_type.component_type("length");
}

/// access length member
/// \param expr: an expression of structured type with length component
/// \param symbol_table: symbol table
/// \return expression representing the "length" member
static exprt get_length(const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(
    expr, "length", get_length_type(expr.type(), symbol_table));
}

/// access data member
/// \param expr: an expression of structured type with data component
/// \param symbol_table: symbol table
/// \return expression representing the "data" member
static exprt get_data(const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(expr, "data", get_data_type(expr.type(), symbol_table));
}

/// we declare a new `cprover_string` whose contents is deduced from the char
/// array.
/// \param array_pointer: an expression of type char array pointer
/// \param loc: location in the source
/// \param function_id: name of the function in which the string is defined
/// \param symbol_table: symbol table
/// \param code: code block, in which some assignments will be added
/// \return a string expression
refined_string_exprt java_string_library_preprocesst::replace_char_array(
  const exprt &array_pointer,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  code_blockt &code)
{
  // array is *array_pointer
  const dereference_exprt array = checked_dereference(array_pointer);
  // array_data is array_pointer-> data
  const exprt array_data = get_data(array, symbol_table);
  const symbolt &sym_char_array = fresh_java_symbol(
    array_data.type(), "char_array", loc, function_id, symbol_table);
  const symbol_exprt char_array = sym_char_array.symbol_expr();
  // char_array = array_pointer->data
  code.add(code_assignt(char_array, array_data), loc);

  // string_expr is `{ rhs->length; string_array }`
  const refined_string_exprt string_expr(
    get_length(array, symbol_table), char_array, refined_string_type);

  const dereference_exprt inf_array(
    char_array, array_typet(java_char_type(), infinity_exprt(java_int_type())));

  add_pointer_to_array_association(
    string_expr.content(), inf_array, symbol_table, loc, function_id, code);

  return string_expr;
}

/// add a symbol with static lifetime and name containing `cprover_string` and
/// given type
/// \param type: a type for refined strings
/// \param loc: a location in the program
/// \param function_id: name of the function in which the code will be added
/// \param symbol_table: symbol table
/// \return a new symbol
symbol_exprt java_string_library_preprocesst::fresh_string(
  const typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table)
{
  symbolt string_symbol =
    fresh_java_symbol(type, "cprover_string", loc, function_id, symbol_table);
  string_symbol.is_static_lifetime=true;
  return string_symbol.symbol_expr();
}

/// Add declaration of a refined string expr whose content and length are
/// fresh symbols.
/// \param loc: source location
/// \param function_id: name of the function in which the string is defined
/// \param symbol_table: the symbol table
/// \param [out] code: code block to which the declaration is added
/// \return refined string expr with fresh content and length symbols
refined_string_exprt java_string_library_preprocesst::decl_string_expr(
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  code_blockt &code)
{
  const symbolt &sym_length = fresh_java_symbol(
    index_type, "cprover_string_length", loc, function_id, symbol_table);
  const symbol_exprt length_field = sym_length.symbol_expr();
  const pointer_typet array_type = pointer_type(java_char_type());
  const symbolt &sym_content = fresh_java_symbol(
    array_type, "cprover_string_content", loc, function_id, symbol_table);
  const symbol_exprt content_field = sym_content.symbol_expr();
  code.add(code_declt(content_field), loc);
  code.add(code_declt{length_field}, loc);
  return refined_string_exprt{length_field, content_field, refined_string_type};
}

/// add symbols with prefix cprover_string_length and cprover_string_data and
/// construct a string_expr from them.
/// \param loc: a location in the program
/// \param function_id: name of the function containing the string
/// \param symbol_table: symbol table
/// \param code: code block to which allocation instruction will be added
/// \return a new string_expr
refined_string_exprt java_string_library_preprocesst::make_nondet_string_expr(
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  code_blockt &code)
{
  /// \todo refactor with initialize_nonddet_string_struct
  const refined_string_exprt str =
    decl_string_expr(loc, function_id, symbol_table, code);

  const side_effect_expr_nondett nondet_length(str.length().type(), loc);
  code.add(code_assignt(str.length(), nondet_length), loc);

  const exprt nondet_array_expr =
    make_nondet_infinite_char_array(symbol_table, loc, function_id, code);

  const address_of_exprt array_pointer(
    index_exprt(nondet_array_expr, from_integer(0, java_int_type())));

  add_pointer_to_array_association(
    array_pointer, nondet_array_expr, symbol_table, loc, function_id, code);

  add_array_to_length_association(
    nondet_array_expr, str.length(), symbol_table, loc, function_id, code);

  code.add(code_assignt(str.content(), array_pointer), loc);

  return refined_string_exprt(str.length(), str.content());
}

/// declare a new String and allocate it
/// \param type: a type for string
/// \param loc: a location in the program
/// \param function_id: function the fresh string is created in
/// \param symbol_table: symbol table
/// \param code: code block to which allocation instruction will be added
/// \return a new string
exprt java_string_library_preprocesst::allocate_fresh_string(
  const typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  code_blockt &code)
{
  const exprt str = fresh_string(type, loc, function_id, symbol_table);

  allocate_objectst allocate_objects(ID_java, loc, function_id, symbol_table);

  code_blockt tmp;
  allocate_objects.allocate_dynamic_object(
    tmp, str, to_reference_type(str.type()).base_type());
  allocate_objects.declare_created_symbols(code);
  code.append(tmp);

  return str;
}

/// assign the result of a function call
/// \param lhs: an expression
/// \param function_id: the name of the function
/// \param arguments: a list of arguments
/// \param symbol_table: a symbol table
/// \return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = <function_id>(arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
static codet code_assign_function_application(
  const exprt &lhs,
  const irep_idt &function_id,
  const exprt::operandst &arguments,
  symbol_table_baset &symbol_table)
{
  return code_assignt(
    lhs,
    make_function_application(
      function_id, arguments, lhs.type(), symbol_table));
}

/// return the result of a function call
/// \param function_id: the name of the function
/// \param arguments: a list of arguments
/// \param type: the return type
/// \param symbol_table: a symbol table
/// \return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// return <function_id>(arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_return_function_application(
  const irep_idt &function_id,
  const exprt::operandst &arguments,
  const typet &type,
  symbol_table_baset &symbol_table)
{
  return code_returnt(
    make_function_application(function_id, arguments, type, symbol_table));
}

/// Declare a fresh symbol of type array of character with infinite size.
/// \param symbol_table: the symbol table
/// \param loc: source location
/// \param function_id: name of the function containing the array
/// \param [out] code: code block where the declaration gets added
/// \return created symbol expression
exprt make_nondet_infinite_char_array(
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  const irep_idt &function_id,
  code_blockt &code)
{
  const array_typet array_type(
    java_char_type(), infinity_exprt(java_int_type()));
  const symbolt data_sym = fresh_java_symbol(
    pointer_type(array_type),
    "nondet_infinite_array_pointer",
    loc,
    function_id,
    symbol_table);

  const symbol_exprt data_pointer = data_sym.symbol_expr();
  code.add(code_declt(data_pointer));
  code.add(make_allocate_code(data_pointer, array_type.size()));
  side_effect_expr_nondett nondet_data{array_type, loc};
  dereference_exprt data{data_pointer};
  code.add(code_assignt{data, std::move(nondet_data)}, loc);
  return std::move(data);
}

/// Add a call to a primitive of the string solver, letting it know that
/// `pointer` points to the first character of `array`.
/// \param pointer: a character pointer expression
/// \param array: a character array expression
/// \param symbol_table: the symbol table
/// \param loc: source location
/// \param function_id: name of the function in which the code will be added
/// \param [out] code: code block to which declaration and calls get added
void add_pointer_to_array_association(
  const exprt &pointer,
  const exprt &array,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  const irep_idt &function_id,
  code_blockt &code)
{
  PRECONDITION(array.type().id() == ID_array);
  PRECONDITION(pointer.type().id() == ID_pointer);
  const symbolt &return_sym = fresh_java_symbol(
    java_int_type(), "return_array", loc, function_id, symbol_table);
  const auto return_expr = return_sym.symbol_expr();
  code.add(code_declt(return_expr), loc);
  code.add(
    code_assign_function_application(
      return_expr,
      ID_cprover_associate_array_to_pointer_func,
      {array, pointer},
      symbol_table),
    loc);
}

/// Add a call to a primitive of the string solver, letting it know that
/// the actual length of `array` is `length`.
/// \param array: infinite size character array expression
/// \param length: integer expression
/// \param symbol_table: the symbol table
/// \param loc: source location
/// \param function_id: name of the function in which the code will be added
/// \param [out] code: code block to which declaration and calls get added
void add_array_to_length_association(
  const exprt &array,
  const exprt &length,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  const irep_idt &function_id,
  code_blockt &code)
{
  const symbolt &return_sym = fresh_java_symbol(
    java_int_type(), "return_array", loc, function_id, symbol_table);
  const auto return_expr = return_sym.symbol_expr();
  code.add(code_declt(return_expr), loc);
  code.add(
    code_assign_function_application(
      return_expr,
      ID_cprover_associate_length_to_array_func,
      {array, length},
      symbol_table),
    loc);
}

/// Add a call to a primitive of the string solver which ensures all characters
/// belong to the character set.
/// \param pointer: a character pointer expression
/// \param length: length of the character sequence pointed by `pointer`
/// \param char_range: character set given by a range expression consisting of
///   two characters separated by an hyphen. For instance "a-z" denotes all
///   lower case ascii letters.
/// \param symbol_table: the symbol table
/// \param loc: source location
/// \param function_id: the name of the function
/// \param [out] code: code block to which declaration and calls get added
void add_character_set_constraint(
  const exprt &pointer,
  const exprt &length,
  const irep_idt &char_range,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  const irep_idt &function_id,
  code_blockt &code)
{
  PRECONDITION(pointer.type().id() == ID_pointer);
  const symbolt &return_sym = fresh_java_symbol(
    java_int_type(), "cnstr_added", loc, function_id, symbol_table);
  const auto return_expr = return_sym.symbol_expr();
  code.add(code_declt(return_expr), loc);
  const constant_exprt char_set_expr(char_range, string_typet());
  code.add(
    code_assign_function_application(
      return_expr,
      ID_cprover_string_constrain_characters_func,
      {length, pointer, char_set_expr},
      symbol_table),
    loc);
}

/// Create a refined_string_exprt `str` whose content and length are fresh
/// symbols, calls the string primitive with name `function_id`.
/// In the arguments of the primitive `str` takes the place of the result and
/// the following arguments are given by parameter `arguments.
/// \param function_id: the name of the function
/// \param arguments: arguments of the function
/// \param loc: source location
/// \param symbol_table: symbol table
/// \param [out] code: gets added the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// int return_code;
/// int str.length;
/// char str.data[str.length]
/// return_code = <function_id>(str.length, str.data, arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// \return refined string expression `str`
refined_string_exprt java_string_library_preprocesst::string_expr_of_function(
  const irep_idt &function_id,
  const exprt::operandst &arguments,
  const source_locationt &loc,
  symbol_table_baset &symbol_table,
  code_blockt &code)
{
  // int return_code;
  const symbolt return_code_sym = fresh_java_symbol(
    java_int_type(),
    std::string("return_code_") + function_id.c_str(),
    loc,
    function_id,
    symbol_table);
  const auto return_code = return_code_sym.symbol_expr();
  code.add(code_declt(return_code), loc);

  const refined_string_exprt string_expr =
    make_nondet_string_expr(loc, function_id, symbol_table, code);

  // args is { str.length, str.content, arguments... }
  exprt::operandst args;
  args.push_back(string_expr.length());
  args.push_back(string_expr.content());
  args.insert(args.end(), arguments.begin(), arguments.end());

  // return_code = <function_id>_data(args)
  code.add(
    code_assign_function_application(
      return_code, function_id, args, symbol_table),
    loc);

  return string_expr;
}

/// Produce code for an assignment of a string expr to a Java string.
/// \param lhs: expression representing the java string to assign to
/// \param rhs_array: pointer to the array to assign
/// \param rhs_length: length of the array to assign
/// \param symbol_table: symbol table
/// \param is_constructor: the assignment happens in the context of a
///   constructor, so the whole object should be initialised, not just its
///   length and data fields.
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = { {Object}, length=rhs_length, data=rhs_array }
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_components_to_java_string(
  const exprt &lhs,
  const exprt &rhs_array,
  const exprt &rhs_length,
  const symbol_table_baset &symbol_table,
  bool is_constructor)
{
  PRECONDITION(implements_java_char_sequence_pointer(lhs.type()));
  dereference_exprt deref = checked_dereference(lhs);

  if(is_constructor)
  {
    // Initialise the supertype with the appropriate classid:
    namespacet ns(symbol_table);
    const struct_typet &lhs_type = to_struct_type(ns.follow(deref.type()));
    auto zero_base_object = *zero_initializer(
      lhs_type.components().front().type(), source_locationt{}, ns);
    set_class_identifier(
      to_struct_expr(zero_base_object), ns, to_struct_tag_type(deref.type()));
    struct_exprt struct_rhs(
      {zero_base_object, rhs_length, rhs_array}, deref.type());
    return code_assignt(checked_dereference(lhs), struct_rhs);
  }
  else
  {
    return code_blockt(
      {code_assignt(get_length(deref, symbol_table), rhs_length),
       code_assignt(get_data(deref, symbol_table), rhs_array)});
  }
}

/// Produce code for an assignemnt of a string expr to a Java string.
/// \param lhs: an expression representing a java string
/// \param rhs: a string expression
/// \param symbol_table: symbol table
/// \param is_constructor: the assignment happens in the context of a
///   constructor, so the whole object should be initialised, not just its
///   length and data fields.
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = { {Object}, length=rhs.length, data=rhs.data }
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_string_expr_to_java_string(
  const exprt &lhs,
  const refined_string_exprt &rhs,
  const symbol_table_baset &symbol_table,
  bool is_constructor)
{
  return code_assign_components_to_java_string(
    lhs, rhs.content(), rhs.length(), symbol_table, is_constructor);
}

/// \param lhs: a string expression
/// \param rhs: an expression representing a java string
/// \param loc: source location
/// \param symbol_table: symbol table
/// \param [out] code: code block that gets appended the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~
/// lhs.length = rhs==null ? 0 : rhs->length
/// lhs.data=rhs->data
/// ~~~~~~~~~~~~~~~~~~~~~~
void java_string_library_preprocesst::code_assign_java_string_to_string_expr(
  const refined_string_exprt &lhs,
  const exprt &rhs,
  const source_locationt &loc,
  const symbol_table_baset &symbol_table,
  code_blockt &code)
{
  PRECONDITION(implements_java_char_sequence_pointer(rhs.type()));

  const dereference_exprt deref = checked_dereference(rhs);

  // Although we should not reach this code if rhs is null, the association
  // `pointer -> length` is added to the solver anyway, so we have to make sure
  // the length is set to something reasonable.
  auto rhs_length = if_exprt(
    equal_exprt(rhs, null_pointer_exprt(to_pointer_type(rhs.type()))),
    from_integer(0, lhs.length().type()),
    get_length(deref, symbol_table));
  rhs_length.set(ID_mode, ID_java);

  // Assignments
  code.add(code_assignt(lhs.length(), rhs_length), loc);
  exprt data_as_array = get_data(deref, symbol_table);
  code.add(code_assignt{lhs.content(), std::move(data_as_array)}, loc);
}

/// Create a string expression whose value is given by a literal
/// \param s: the literal to be assigned
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param [out] code: gets added the following:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// tmp_string = "<s>"
/// lhs = cprover_string_literal_func(tmp_string)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// \return a new refined string
refined_string_exprt
java_string_library_preprocesst::string_literal_to_string_expr(
  const std::string &s,
  const source_locationt &loc,
  symbol_table_baset &symbol_table,
  code_blockt &code)
{
  return string_expr_of_function(
    ID_cprover_string_literal_func,
    {constant_exprt{s, string_typet{}}},
    loc,
    symbol_table,
    code);
}

/// Provide code for the String.valueOf(F) function.
/// \param type: type of the function call
/// \param loc: location in the program_invocation_name
/// \param function_id: function the generated code will be added to
/// \param symbol_table: symbol table
/// \param message_handler: a message handler
/// \return Code corresponding to the Java conversion of floats to strings.
code_blockt java_string_library_preprocesst::make_float_to_string_code(
  const java_method_typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  (void)message_handler;

  // Getting the argument
  java_method_typet::parameterst params = type.parameters();
  PRECONDITION(params.size()==1);
  PRECONDITION(!params[0].get_identifier().empty());
  const symbol_exprt arg(params[0].get_identifier(), params[0].type());

  // Holder for output code
  code_blockt code;

  // Declaring and allocating String * str
  const exprt str = allocate_fresh_string(
    type.return_type(), loc, function_id, symbol_table, code);

  // Expression representing 0.0
  const ieee_float_spect float_spec{to_floatbv_type(params[0].type())};
  ieee_floatt zero_float(float_spec);
  zero_float.from_float(0.0);
  const constant_exprt zero = zero_float.to_expr();

  // For each possible case with have a condition and a string_exprt
  std::vector<exprt> condition_list;
  std::vector<refined_string_exprt> string_expr_list;

  // Case of computerized scientific notation
  condition_list.push_back(binary_relation_exprt(arg, ID_ge, zero));
  const refined_string_exprt sci_notation = string_expr_of_function(
    ID_cprover_string_of_float_scientific_notation_func,
    {arg},
    loc,
    symbol_table,
    code);
  string_expr_list.push_back(sci_notation);

  // Subcase of negative scientific notation
  condition_list.push_back(binary_relation_exprt(arg, ID_lt, zero));
  const refined_string_exprt minus_sign =
    string_literal_to_string_expr("-", loc, symbol_table, code);
  const refined_string_exprt neg_sci_notation = string_expr_of_function(
    ID_cprover_string_concat_func,
    {minus_sign, sci_notation},
    loc,
    symbol_table,
    code);
  string_expr_list.push_back(neg_sci_notation);

  // Case of NaN
  condition_list.push_back(isnan_exprt(arg));
  const refined_string_exprt nan =
    string_literal_to_string_expr("NaN", loc, symbol_table, code);
  string_expr_list.push_back(nan);

  // Case of Infinity
  extractbit_exprt is_neg(arg, float_spec.width()-1);
  condition_list.push_back(and_exprt(isinf_exprt(arg), not_exprt(is_neg)));
  const refined_string_exprt infinity =
    string_literal_to_string_expr("Infinity", loc, symbol_table, code);
  string_expr_list.push_back(infinity);

  // Case -Infinity
  condition_list.push_back(and_exprt(isinf_exprt(arg), is_neg));
  const refined_string_exprt minus_infinity =
    string_literal_to_string_expr("-Infinity", loc, symbol_table, code);
  string_expr_list.push_back(minus_infinity);

  // Case of 0.0
  // Note: for zeros we must use equal_exprt and not ieee_float_equal_exprt,
  // the latter disregards the sign
  condition_list.push_back(equal_exprt(arg, zero));
  const refined_string_exprt zero_string =
    string_literal_to_string_expr("0.0", loc, symbol_table, code);
  string_expr_list.push_back(zero_string);

  // Case of -0.0
  ieee_floatt minus_zero_float(float_spec);
  minus_zero_float.from_float(-0.0f);
  condition_list.push_back(equal_exprt(arg, minus_zero_float.to_expr()));
  const refined_string_exprt minus_zero_string =
    string_literal_to_string_expr("-0.0", loc, symbol_table, code);
  string_expr_list.push_back(minus_zero_string);

  // Case of simple notation
  ieee_floatt bound_inf_float(float_spec);
  ieee_floatt bound_sup_float(float_spec);
  bound_inf_float.from_float(1e-3f);
  bound_sup_float.from_float(1e7f);
  bound_inf_float.change_spec(float_spec);
  bound_sup_float.change_spec(float_spec);
  const constant_exprt bound_inf = bound_inf_float.to_expr();
  const constant_exprt bound_sup = bound_sup_float.to_expr();

  const and_exprt is_simple_float{binary_relation_exprt(arg, ID_ge, bound_inf),
                                  binary_relation_exprt(arg, ID_lt, bound_sup)};
  condition_list.push_back(is_simple_float);

  const refined_string_exprt simple_notation = string_expr_of_function(
    ID_cprover_string_of_float_func, {arg}, loc, symbol_table, code);
  string_expr_list.push_back(simple_notation);

  // Case of a negative number in simple notation
  const and_exprt is_neg_simple_float{
    binary_relation_exprt(arg, ID_le, unary_minus_exprt(bound_inf)),
    binary_relation_exprt(arg, ID_gt, unary_minus_exprt(bound_sup))};
  condition_list.push_back(is_neg_simple_float);

  const refined_string_exprt neg_simple_notation = string_expr_of_function(
    ID_cprover_string_concat_func,
    {minus_sign, simple_notation},
    loc,
    symbol_table,
    code);
  string_expr_list.push_back(neg_simple_notation);

  // Combining all cases
  INVARIANT(
    string_expr_list.size()==condition_list.size(),
    "number of created strings should correspond to number of conditions");

  // We do not check the condition of the first element in the list as it
  // will be reached only if all other conditions are not satisfied.
  codet tmp_code = code_assign_string_expr_to_java_string(
    str, string_expr_list[0], symbol_table, true);
  for(std::size_t i=1; i<condition_list.size(); i++)
  {
    tmp_code = code_ifthenelset(
      condition_list[i],
      code_assign_string_expr_to_java_string(
        str, string_expr_list[i], symbol_table, true),
      tmp_code);
  }
  code.add(tmp_code, loc);

  // Return str
  code.add(code_returnt(str), loc);
  return code;
}

/// Generate the goto code for string initialization.
/// \param function_id: name of the function to be called
/// \param type: the type of the function call
/// \param loc: location in program
/// \param symbol_table: the symbol table to populate
/// \param is_constructor: the function being made is a constructor, so the
///   whole object should be initialised, not just its length and data fields.
/// \return code for the `String.<init>(args)` function:
///
///     cprover_string_length = fun(arg).length;
///     cprover_string_array = fun(arg).data;
///     this->length = cprover_string_length;
///     this->data = cprover_string_array;
///     cprover_string = {.=cprover_string_length, .=cprover_string_array};
///
code_blockt java_string_library_preprocesst::make_init_function_from_call(
  const irep_idt &function_id,
  const java_method_typet &type,
  const source_locationt &loc,
  symbol_table_baset &symbol_table,
  bool is_constructor)
{
  java_method_typet::parameterst params = type.parameters();

  // The first parameter is the object to be initialized
  PRECONDITION(!params.empty());
  PRECONDITION(!params[0].get_identifier().empty());
  const symbol_exprt arg_this(params[0].get_identifier(), params[0].type());
  if(is_constructor)
    params.erase(params.begin());

  // Holder for output code
  code_blockt code;

  // Processing parameters
  const exprt::operandst args =
    process_parameters(params, loc, function_id, symbol_table, code);

  // string_expr <- function(arg1)
  const refined_string_exprt string_expr =
    string_expr_of_function(function_id, args, loc, symbol_table, code);

  // arg_this <- string_expr
  code.add(
    code_assign_string_expr_to_java_string(
      arg_this, string_expr, symbol_table, is_constructor),
    loc);

  return code;
}

/// Call a cprover internal function, assign the result to object `this` and
/// return it.
/// \param function_id: name of the function to be called
/// \param type: the type of the function call
/// \param loc: location in program
/// \param symbol_table: the symbol table to populate
/// \return Code calling function with the given function name.
code_blockt
java_string_library_preprocesst::make_assign_and_return_function_from_call(
  const irep_idt &function_id,
  const java_method_typet &type,
  const source_locationt &loc,
  symbol_table_baset &symbol_table)
{
  // This is similar to assign functions except we return a pointer to `this`
  const java_method_typet::parameterst &params = type.parameters();
  PRECONDITION(!params.empty());
  PRECONDITION(!params[0].get_identifier().empty());
  code_blockt code;
  code.add(
    make_assign_function_from_call(function_id, type, loc, symbol_table), loc);
  const symbol_exprt arg_this(params[0].get_identifier(), params[0].type());
  code.add(code_returnt(arg_this), loc);
  return code;
}

/// Call a cprover internal function and assign the result to object `this`.
/// \param function_id: name of the function to be called
/// \param type: the type of the function call
/// \param loc: location in program
/// \param symbol_table: the symbol table to populate
/// \return Code assigning result of a call to the function with given function
///   name.
code_blockt java_string_library_preprocesst::make_assign_function_from_call(
  const irep_idt &function_id,
  const java_method_typet &type,
  const source_locationt &loc,
  symbol_table_baset &symbol_table)
{
  // This is similar to initialization function except we do not ignore
  // the first argument
  return make_init_function_from_call(
    function_id, type, loc, symbol_table, false);
}

/// Used to provide our own implementation of the CProver.classIdentifier()
/// function.
/// \param type: type of the function called
/// \param loc: location in the source
/// \param function_id: function the generated code will be added to
/// \param symbol_table: the symbol table
/// \param message_handler: a message handler
/// \return Code corresponding to
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr1 = substr(obj->@class_identifier, 6)
/// return string_expr1;
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
code_blockt java_string_library_preprocesst::make_class_identifier_code(
  const java_method_typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  java_method_typet::parameterst params = type.parameters();
  PRECONDITION(!params.empty());
  PRECONDITION(!params[0].get_identifier().empty());
  const symbol_exprt obj(params[0].get_identifier(), params[0].type());

  // Code to be returned
  code_blockt code;

  // class_identifier is obj->@class_identifier
  const member_exprt class_identifier{
    checked_dereference(obj), JAVA_CLASS_IDENTIFIER_FIELD_NAME, string_typet()};

  // string_expr = cprover_string_literal(this->@class_identifier)
  const refined_string_exprt string_expr = string_expr_of_function(
    ID_cprover_string_literal_func,
    {class_identifier},
    loc,
    symbol_table,
    code);

  // string_expr1 = substr(string_expr, 6)
  // We do this to remove the "java::" prefix
  const refined_string_exprt string_expr1 = string_expr_of_function(
    ID_cprover_string_substring_func,
    {string_expr, from_integer(6, java_int_type())},
    loc,
    symbol_table,
    code);

  // string1 = (String*) string_expr
  const typet &string_ptr_type = type.return_type();
  const exprt string1 = allocate_fresh_string(
    string_ptr_type, loc, function_id, symbol_table, code);
  code.add(
    code_assign_string_expr_to_java_string(
      string1, string_expr1, symbol_table, true),
    loc);

  // > return string1;
  code.add(code_returnt{string1}, loc);
  return code;
}

/// Provide code for a function that calls a function from the solver and simply
/// returns it.
/// \param function_id: name of the function to be called
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~
/// return function_id(args)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~
code_blockt java_string_library_preprocesst::make_function_from_call(
  const irep_idt &function_id,
  const java_method_typet &type,
  const source_locationt &loc,
  symbol_table_baset &symbol_table)
{
  code_blockt code;
  const exprt::operandst args =
    process_parameters(type.parameters(), loc, function_id, symbol_table, code);
  code.add(
    code_return_function_application(
      function_id, args, type.return_type(), symbol_table),
    loc);
  return code;
}

/// Provide code for a function that calls a function from the solver and return
/// the string_expr result as a Java string.
/// \param function_id: name of the function to be called
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr = function_id(args)
/// string = new String
/// string = string_expr_to_string(string)
/// return string
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
code_blockt
java_string_library_preprocesst::make_string_returning_function_from_call(
  const irep_idt &function_id,
  const java_method_typet &type,
  const source_locationt &loc,
  symbol_table_baset &symbol_table)
{
  // Code for the output
  code_blockt code;

  // Calling the function
  const exprt::operandst arguments =
    process_parameters(type.parameters(), loc, function_id, symbol_table, code);

  // String expression that will hold the result
  const refined_string_exprt string_expr =
    string_expr_of_function(function_id, arguments, loc, symbol_table, code);

  // Assign to string
  const exprt str = allocate_fresh_string(
    type.return_type(), loc, function_id, symbol_table, code);
  code.add(
    code_assign_string_expr_to_java_string(
      str, string_expr, symbol_table, true),
    loc);

  // Return value
  code.add(code_returnt(str), loc);
  return code;
}

/// Generates code for a function which copies a string object to a new string
/// object.
/// \param type: type of the function
/// \param loc: location in the source
/// \param function_id: function the generated code will be added to
/// \param symbol_table: symbol table
/// \param message_handler: a message handler
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr = string_to_string_expr(arg0)
/// string_expr_sym = { string_expr.length; string_expr.content }
/// str = new String
/// str = string_expr_to_string(string_expr)
/// return str
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
code_blockt java_string_library_preprocesst::make_copy_string_code(
  const java_method_typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  (void)message_handler;

  // Code for the output
  code_blockt code;

  // String expression that will hold the result
  const refined_string_exprt string_expr =
    decl_string_expr(loc, function_id, symbol_table, code);

  // Assign the argument to string_expr
  const java_method_typet::parametert &op = type.parameters()[0];
  PRECONDITION(!op.get_identifier().empty());
  const symbol_exprt arg0{op.get_identifier(), op.type()};
  code_assign_java_string_to_string_expr(
    string_expr, arg0, loc, symbol_table, code);

  // Allocate and assign the string
  const exprt str = allocate_fresh_string(
    type.return_type(), loc, function_id, symbol_table, code);
  code.add(
    code_assign_string_expr_to_java_string(
      str, string_expr, symbol_table, true),
    loc);

  // Return value
  code.add(code_returnt(str), loc);
  return code;
}

/// Generates code for a constructor of a string object from another string
/// object.
/// \param type: type of the function
/// \param loc: location in the source
/// \param function_id: name of the function (used for variable naming) where
///   the generated code ends up.
/// \param symbol_table: symbol table
/// \param message_handler: a message handler
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr = java_string_to_string_expr(arg1)
/// string_expr_sym = { string_expr.length; string_expr.content }
/// this = string_expr_to_java_string(string_expr)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
code_blockt java_string_library_preprocesst::make_copy_constructor_code(
  const java_method_typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  (void)message_handler;

  code_blockt copy_constructor_body;

  // String expression that will hold the result
  const refined_string_exprt string_expr =
    decl_string_expr(loc, function_id, symbol_table, copy_constructor_body);

  // Assign argument to a string_expr
  const java_method_typet::parameterst &params = type.parameters();
  PRECONDITION(!params[0].get_identifier().empty());
  PRECONDITION(!params[1].get_identifier().empty());
  const symbol_exprt arg1{params[1].get_identifier(), params[1].type()};
  code_assign_java_string_to_string_expr(
    string_expr, arg1, loc, symbol_table, copy_constructor_body);

  // Assign string_expr to `this` object
  const symbol_exprt arg_this{params[0].get_identifier(), params[0].type()};
  copy_constructor_body.add(
    code_assign_string_expr_to_java_string(
      arg_this, string_expr, symbol_table, true),
    loc);

  return copy_constructor_body;
}

/// Generates code for the String.length method
/// \param type: type of the function
/// \param loc: location in the source
/// \param function_id: unused
/// \param symbol_table: symbol table
/// \param message_handler: a message handler
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// str_expr = java_string_to_string_expr(this)
/// str_expr_sym = str_expr
/// return this->length
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
code_returnt java_string_library_preprocesst::make_string_length_code(
  const java_method_typet &type,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  (void)function_id;
  (void)message_handler;

  const java_method_typet::parameterst &params = type.parameters();
  PRECONDITION(!params[0].get_identifier().empty());
  const symbol_exprt arg_this{params[0].get_identifier(), params[0].type()};
  const dereference_exprt deref = checked_dereference(arg_this);

  code_returnt ret(get_length(deref, symbol_table));
  ret.add_source_location() = loc;

  return ret;
}

bool java_string_library_preprocesst::implements_function(
  const irep_idt &function_id) const
{
  for(const id_mapt *map : id_maps)
    if(map->count(function_id) != 0)
      return true;

  return conversion_table.count(function_id) != 0;
}

template <typename TMap, typename TContainer>
void add_keys_to_container(const TMap &map, TContainer &container)
{
  static_assert(
    std::is_same<typename TMap::key_type,
                 typename TContainer::value_type>::value,
    "TContainer value_type doesn't match TMap key_type");
  std::transform(
    map.begin(),
    map.end(),
    std::inserter(container, container.begin()),
    [](const typename TMap::value_type &pair) { return pair.first; });
}

void java_string_library_preprocesst::get_all_function_names(
  std::unordered_set<irep_idt> &methods) const
{
  for(const id_mapt *map : id_maps)
    add_keys_to_container(*map, methods);

  add_keys_to_container(conversion_table, methods);
}

/// Should be called to provide code for string functions that are used in the
/// code but for which no implementation is provided.
/// \param symbol: symbol of the function to provide code for
/// \param symbol_table: a symbol table
/// \param message_handler: a message handler
/// \return Code for the body of the String functions if they are part of the
///   supported String functions, nil_exprt otherwise.
codet java_string_library_preprocesst::code_for_function(
  const symbolt &symbol,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  const irep_idt &function_id = symbol.name;
  const java_method_typet &type = to_java_method_type(symbol.type);
  const source_locationt &loc = symbol.location;
  auto it_id=cprover_equivalent_to_java_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_function.end())
    return make_function_from_call(it_id->second, type, loc, symbol_table);

  it_id=cprover_equivalent_to_java_string_returning_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_string_returning_function.end())
    return make_string_returning_function_from_call(
      it_id->second, type, loc, symbol_table);

  it_id=cprover_equivalent_to_java_constructor.find(function_id);
  if(it_id!=cprover_equivalent_to_java_constructor.end())
    return make_init_function_from_call(
      it_id->second, type, loc, symbol_table);

  it_id=cprover_equivalent_to_java_assign_and_return_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_assign_and_return_function.end())
    return make_assign_and_return_function_from_call(
      it_id->second, type, loc, symbol_table);

  it_id=cprover_equivalent_to_java_assign_function.find(function_id);
  if(it_id!=cprover_equivalent_to_java_assign_function.end())
    return make_assign_function_from_call(
      it_id->second, type, loc, symbol_table);

  auto it=conversion_table.find(function_id);
  INVARIANT(
    it != conversion_table.end(), "Couldn't retrieve code for string method");

  return it->second(type, loc, function_id, symbol_table, message_handler);
}

/// Check whether a class name is known as a string type.
/// \param class_name: name of the class
/// \return True if the type is one that is known to our preprocessing, false
///   otherwise
bool java_string_library_preprocesst::is_known_string_type(
  irep_idt class_name)
{
  return string_types.find(class_name)!=string_types.end();
}

void java_string_library_preprocesst::initialize_known_type_table()
{
  string_types = std::unordered_set<irep_idt>{"java.lang.String",
                                              "java.lang.StringBuilder",
                                              "java.lang.CharSequence",
                                              "java.lang.StringBuffer"};
}

/// fill maps with correspondence from java method names to conversion functions
void java_string_library_preprocesst::initialize_conversion_table()
{
  character_preprocess.initialize_conversion_table();

  // The following list of function is organized by libraries, with
  // constructors first and then methods in alphabetic order.
  // Methods that are not supported here should ultimately have Java models
  // provided for them in the class-path.

  // CProverString library
  cprover_equivalent_to_java_assign_and_return_function
    ["java::org.cprover.CProverString.append:(Ljava/lang/StringBuilder;Ljava/"
     "lang/CharSequence;II)"
     "Ljava/lang/StringBuilder;"] = ID_cprover_string_concat_func;
  // CProverString.charAt differs from the Java String.charAt in that no
  // exception is raised for the out of bounds case.
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.charAt:(Ljava/lang/String;I)C"] =
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.charAt:(Ljava/lang/StringBuffer;I)C"] =
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.codePointAt:(Ljava/lang/String;I)I"] =
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.codePointBefore:(Ljava/lang/String;I)I"] =
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.codePointCount:(Ljava/lang/String;II)I"] =
      ID_cprover_string_code_point_count_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::org.cprover.CProverString.delete:(Ljava/lang/StringBuffer;II)Ljava/"
     "lang/StringBuffer;"] = ID_cprover_string_delete_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::org.cprover.CProverString.delete:(Ljava/lang/"
     "StringBuilder;II)Ljava/lang/StringBuilder;"] =
      ID_cprover_string_delete_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::org.cprover.CProverString.deleteCharAt:(Ljava/lang/"
     "StringBuffer;I)Ljava/lang/StringBuffer;"] =
      ID_cprover_string_delete_char_at_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::org.cprover.CProverString.deleteCharAt:(Ljava/lang/"
     "StringBuilder;I)Ljava/lang/StringBuilder;"] =
      ID_cprover_string_delete_char_at_func;

  std::string format_signature = "java::org.cprover.CProverString.format:(";
  for(std::size_t i = 0; i < MAX_FORMAT_ARGS + 1; ++i)
    format_signature += "Ljava/lang/String;";
  format_signature += ")Ljava/lang/String;";
  cprover_equivalent_to_java_string_returning_function[format_signature] =
    ID_cprover_string_format_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::org.cprover.CProverString.insert:(Ljava/lang/StringBuilder;ILjava/"
     "lang/String;)Ljava/lang/StringBuilder;"] = ID_cprover_string_insert_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.offsetByCodePoints:(Ljava/lang/"
     "String;II)I"] = ID_cprover_string_offset_by_code_point_func;
  cprover_equivalent_to_java_assign_function
    ["java::org.cprover.CProverString.setCharAt:(Ljava/lang/"
     "StringBuffer;IC)V"] = ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_function
    ["java::org.cprover.CProverString.setCharAt:(Ljava/lang/"
     "StringBuilder;IC)V"] = ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_function
    ["java::org.cprover.CProverString.setLength:(Ljava/lang/StringBuffer;I)V"] =
      ID_cprover_string_set_length_func;
  cprover_equivalent_to_java_assign_function
    ["java::org.cprover.CProverString.setLength:(Ljava/lang/"
     "StringBuilder;I)V"] = ID_cprover_string_set_length_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.subSequence:(Ljava/lang/String;II)Ljava/"
     "lang/CharSequence;"] = ID_cprover_string_substring_func;
  // CProverString.substring differs from the Java String.substring in that no
  // exception is raised for the out of bounds case.
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.substring:(Ljava/lang/String;I)"
     "Ljava/lang/String;"] = ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.substring:(Ljava/lang/String;II)"
     "Ljava/lang/String;"] = ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.substring:(Ljava/Lang/"
     "StringBuffer;II)Ljava/lang/String;"] = ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.toString:(I)Ljava/lang/String;"] =
      ID_cprover_string_of_int_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.toString:(II)Ljava/lang/String;"] =
      ID_cprover_string_of_int_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.toString:(J)Ljava/lang/String;"] =
      ID_cprover_string_of_long_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::org.cprover.CProverString.toString:(JI)Ljava/lang/String;"] =
      ID_cprover_string_of_long_func;
  conversion_table
    ["java::org.cprover.CProverString.toString:(F)Ljava/lang/String;"] =
      std::bind(
        &java_string_library_preprocesst::make_float_to_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3,
        std::placeholders::_4,
        std::placeholders::_5);
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.parseInt:(Ljava/lang/String;I)I"] =
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.parseLong:(Ljava/lang/String;I)J"] =
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.isValidInt:(Ljava/lang/String;I)Z"] =
      ID_cprover_string_is_valid_int_func;
  cprover_equivalent_to_java_function
    ["java::org.cprover.CProverString.isValidLong:(Ljava/lang/String;I)Z"] =
      ID_cprover_string_is_valid_long_func;

  // String library
  conversion_table["java::java.lang.String.<init>:(Ljava/lang/String;)V"] =
    std::bind(
      &java_string_library_preprocesst::make_copy_constructor_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);
  conversion_table
    ["java::java.lang.String.<init>:(Ljava/lang/StringBuilder;)V"] = std::bind(
      &java_string_library_preprocesst::make_copy_constructor_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);
  cprover_equivalent_to_java_constructor
    ["java::java.lang.String.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_function
    ["java::java.lang.String.compareTo:(Ljava/lang/String;)I"]=
      ID_cprover_string_compare_to_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.concat:(Ljava/lang/String;)Ljava/lang/String;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z"]=
    ID_cprover_string_contains_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.endsWith:(Ljava/lang/String;)Z"]=
      ID_cprover_string_endswith_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.equalsIgnoreCase:(Ljava/lang/String;)Z"]=
      ID_cprover_string_equals_ignore_case_func;

  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(I)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(II)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(Ljava/lang/String;)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.indexOf:(Ljava/lang/String;I)I"]=
      ID_cprover_string_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.isEmpty:()Z"]=
      ID_cprover_string_is_empty_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(I)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(II)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(Ljava/lang/String;)I"]=
      ID_cprover_string_last_index_of_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.lastIndexOf:(Ljava/lang/String;I)I"]=
      ID_cprover_string_last_index_of_func;
  conversion_table["java::java.lang.String.length:()I"] = std::bind(
    &java_string_library_preprocesst::make_string_length_code,
    this,
    std::placeholders::_1,
    std::placeholders::_2,
    std::placeholders::_3,
    std::placeholders::_4,
    std::placeholders::_5);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.replace:(CC)Ljava/lang/String;"]=
      ID_cprover_string_replace_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.replace:(Ljava/lang/CharSequence;Ljava/lang/CharSequence;)Ljava/lang/String;"]= // NOLINT
      ID_cprover_string_replace_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.startsWith:(Ljava/lang/String;)Z"]=
      ID_cprover_string_startswith_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.startsWith:(Ljava/lang/String;I)Z"]=
      ID_cprover_string_startswith_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.toLowerCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_lower_case_func;
  conversion_table["java::java.lang.String.toString:()Ljava/lang/String;"] =
    std::bind(
      &java_string_library_preprocesst::make_copy_string_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.toUpperCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_upper_case_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.trim:()Ljava/lang/String;"]=
      ID_cprover_string_trim_func;

  // StringBuilder library
  conversion_table
    ["java::java.lang.StringBuilder.<init>:(Ljava/lang/String;)V"] = std::bind(
      &java_string_library_preprocesst::make_copy_constructor_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);
  conversion_table
    ["java::java.lang.StringBuilder.<init>:(Ljava/lang/CharSequence;)V"] =
      std::bind(
        &java_string_library_preprocesst::make_copy_constructor_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3,
        std::placeholders::_4,
        std::placeholders::_5);
  cprover_equivalent_to_java_constructor
    ["java::java.lang.StringBuilder.<init>:()V"]=
      ID_cprover_string_empty_string_func;
  cprover_equivalent_to_java_constructor
    ["java::java.lang.StringBuilder.<init>:(I)V"] =
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/CharSequence;)"
     "Ljava/lang/StringBuilder;"] = ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/String;)"
     "Ljava/lang/StringBuilder;"] = ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/StringBuffer;)"
     "Ljava/lang/StringBuilder;"] = ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.appendCodePoint:(I)"
     "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_code_point_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  conversion_table["java::java.lang.StringBuilder.length:()I"] = std::bind(
    &java_string_library_preprocesst::make_string_length_code,
    this,
    std::placeholders::_1,
    std::placeholders::_2,
    std::placeholders::_3,
    std::placeholders::_4,
    std::placeholders::_5);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuilder.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuilder.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  conversion_table
    ["java::java.lang.StringBuilder.toString:()Ljava/lang/String;"] = std::bind(
      &java_string_library_preprocesst::make_copy_string_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);

  // StringBuffer library
  conversion_table
    ["java::java.lang.StringBuffer.<init>:(Ljava/lang/String;)V"] = std::bind(
      &java_string_library_preprocesst::make_copy_constructor_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);
  cprover_equivalent_to_java_constructor
    ["java::java.lang.StringBuffer.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Ljava/lang/StringBuffer;)"
     "Ljava/lang/StringBuffer;"] = ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.appendCodePoint:(I)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_code_point_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  conversion_table
    ["java::java.lang.StringBuffer.length:()I"]=
      conversion_table["java::java.lang.String.length:()I"];
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuffer.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  conversion_table
    ["java::java.lang.StringBuffer.toString:()Ljava/lang/String;"] = std::bind(
      &java_string_library_preprocesst::make_copy_string_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);

  // CharSequence library
  cprover_equivalent_to_java_function
    ["java::java.lang.CharSequence.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  conversion_table
    ["java::java.lang.CharSequence.toString:()Ljava/lang/String;"] = std::bind(
      &java_string_library_preprocesst::make_copy_string_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3,
      std::placeholders::_4,
      std::placeholders::_5);
  conversion_table
    ["java::java.lang.CharSequence.length:()I"]=
      conversion_table["java::java.lang.String.length:()I"];

  // Other libraries
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.Integer.toHexString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_hex_func;
  conversion_table
    ["java::org.cprover.CProver.classIdentifier:("
     "Ljava/lang/Object;)Ljava/lang/String;"] =
      std::bind(
        &java_string_library_preprocesst::make_class_identifier_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3,
        std::placeholders::_4,
        std::placeholders::_5);
}
