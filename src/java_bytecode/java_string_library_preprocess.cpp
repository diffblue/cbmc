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

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/fresh_symbol.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>
#include "java_types.h"
#include "java_object_factory.h"

#include "java_string_library_preprocess.h"

/// \param type: a type
/// \param tag: a string
/// \return Boolean telling whether the type is a struct with the given tag or a
///   symbolic type with the tag prefixed by "java::"
bool java_string_library_preprocesst::java_type_matches_tag(
  const typet &type, const std::string &tag)
{
  if(type.id()==ID_symbol)
  {
    irep_idt tag_id=to_symbol_type(type).get_identifier();
    return tag_id=="java::"+tag;
  }
  else if(type.id()==ID_struct)
  {
    irep_idt tag_id=to_struct_type(type).get_tag();
    return tag_id==tag;
  }
  return false;
}

/// \param type: a type
/// \return Boolean telling whether the type is that of java string pointer
bool java_string_library_preprocesst::is_java_string_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_type(subtype);
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
    const typet &subtype=pt.subtype();
    return is_java_string_builder_type(subtype);
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
    const typet &subtype=pt.subtype();
    return is_java_string_buffer_type(subtype);
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
    const typet &subtype=pt.subtype();
    return is_java_char_sequence_type(subtype);
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
    const typet &subtype=pt.subtype();
    return is_java_char_array_type(subtype);
  }
  return false;
}

/// \param symbol_table: a symbol_table containing an entry for java Strings
/// \return the type of data fields in java Strings.
typet string_data_type(symbol_tablet symbol_table)
{
  symbolt sym=symbol_table.lookup("java::java.lang.String");
  typet concrete_type=sym.type;
  struct_typet struct_type=to_struct_type(concrete_type);
  std::size_t index=struct_type.component_number("data");
  typet data_type=struct_type.components()[index].type();
  return data_type;
}

/// \return the type of the length field in java Strings.
typet string_length_type()
{
  return java_int_type();
}

/// Add to the symbol table type declaration for a String-like Java class.
/// \param class_name: a name for the class such as "java.lang.String"
/// \param symbol_table: symbol table to which the class will be added
void java_string_library_preprocesst::add_string_type(
  const irep_idt &class_name, symbol_tablet &symbol_table)
{
  class_typet string_type;
  string_type.set_tag(class_name);
  string_type.components().resize(3);
  string_type.components()[0].set_name("@java.lang.Object");
  string_type.components()[0].set_pretty_name("@java.lang.Object");
  string_type.components()[0].type()=symbol_typet("java::java.lang.Object");
  string_type.components()[1].set_name("length");
  string_type.components()[1].set_pretty_name("length");
  string_type.components()[1].type()=string_length_type();
  string_type.components()[2].set_name("data");
  string_type.components()[2].set_pretty_name("data");
  // Use a pointer-to-unbounded-array instead of a pointer-to-char.
  // Saves some casting in the string refinement algorithm but may
  // be unnecessary.
  string_type.components()[2].type()=pointer_typet(
    array_typet(java_char_type(), infinity_exprt(string_length_type())));
  string_type.add_base(symbol_typet("java::java.lang.Object"));

  symbolt tmp_string_symbol;
  tmp_string_symbol.name="java::"+id2string(class_name);
  symbolt *string_symbol=nullptr;
  symbol_table.move(tmp_string_symbol, string_symbol);
  string_symbol->base_name=id2string(class_name);
  string_symbol->pretty_name=id2string(class_name);
  string_symbol->type=string_type;
  string_symbol->is_type=true;
}

/// add a symbol in the table with static lifetime and name containing
/// `cprover_string_array` and given type
/// \param type: an array type
/// \param location: a location in the program
/// \param symbol_table: symbol table
symbol_exprt java_string_library_preprocesst::fresh_array(
  const typet &type,
  const source_locationt &location,
  symbol_tablet &symbol_table)
{
  symbolt array_symbol=get_fresh_aux_symbol(
    type,
    "cprover_string_array",
    "cprover_string_array",
    location,
    ID_java,
    symbol_table);
  array_symbol.is_static_lifetime=true;
  return array_symbol.symbol_expr();
}

/// declare a function with the given name and type
/// \param function_name: a name
/// \param type: a type
/// \param symbol_table: symbol table
void java_string_library_preprocesst::declare_function(
  irep_idt function_name, const typet &type, symbol_tablet &symbol_table)
{
  auxiliary_symbolt func_symbol;
  func_symbol.base_name=function_name;
  func_symbol.pretty_name=function_name;
  func_symbol.is_static_lifetime=false;
  func_symbol.mode=ID_java;
  func_symbol.name=function_name;
  func_symbol.type=type;
  symbol_table.add(func_symbol);
}

/// calls string_refine_preprocesst::process_operands with a list of parameters.
/// \param params: a list of function parameters
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param init_code: code block, in which declaration of some arguments may be
///   added
/// \return a list of expressions
exprt::operandst java_string_library_preprocesst::process_parameters(
  const code_typet::parameterst &params,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : params)
  {
    symbol_exprt sym(p.get_identifier(), p.type());
    ops.push_back(sym);
  }
  return process_operands(ops, loc, symbol_table, init_code);
}

/// Creates a string_exprt from the input exprt and adds it to processed_ops
/// \param processed_ops: the list of processed operands to populate
/// \param op_to_process: a list of expressions
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param init_code: code block, in which declaration of some arguments may be
///   added
void java_string_library_preprocesst::process_single_operand(
  exprt::operandst &processed_ops,
  const exprt &op_to_process,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  member_exprt length(
    op_to_process, "length", string_length_type());
  member_exprt data(op_to_process, "data", string_data_type(symbol_table));
  dereference_exprt deref_data(data, data.type().subtype());
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, init_code);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, init_code);
  init_code.add(code_declt(string_expr_sym));
  init_code.add(code_assignt(string_expr.length(), length));
  init_code.add(
    code_assignt(string_expr.content(), deref_data));
  init_code.add(code_assignt(string_expr_sym, string_expr));
  processed_ops.push_back(string_expr);
}

/// for each expression that is of a type implementing strings, we declare a new
/// `cprover_string` whose contents is deduced from the expression and replace
/// the expression by this cprover_string in the output list; in the other case
/// the expression is kept as is for the output list. Also does the same thing
/// for char array references.
/// \param operands: a list of expressions
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param init_code: code block, in which declaration of some arguments may be
///   added
/// \return a list of expressions
exprt::operandst java_string_library_preprocesst::process_operands(
  const exprt::operandst &operands,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  exprt::operandst ops;
  for(const auto &p : operands)
  {
    if(implements_java_char_sequence(p.type()))
    {
      dereference_exprt deref(p, to_pointer_type(p.type()).subtype());
      process_single_operand(ops, deref, loc, symbol_table, init_code);
    }
    else if(is_java_char_array_pointer_type(p.type()))
    {
      ops.push_back(replace_char_array(p, loc, symbol_table, init_code));
    }
    else
    {
      ops.push_back(p);
    }
  }
  return ops;
}

/// Converts the operands of the equals function to string expressions and
/// outputs these conversions. As a side effect of the conversions it adds some
/// code to init_code.
/// \param operands: a list of expressions
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param init_code: code block, in which declaration of some arguments may be
///   added
/// \return a list of expressions
exprt::operandst
  java_string_library_preprocesst::process_equals_function_operands(
  const exprt::operandst &operands,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  assert(operands.size()==2);
  exprt::operandst ops;
  exprt op0=operands[0];
  exprt op1=operands[1];

  assert(implements_java_char_sequence(op0.type()));
  dereference_exprt deref0(op0, to_pointer_type(op0.type()).subtype());
  process_single_operand(ops, deref0, loc, symbol_table, init_code);

  // TODO: Manage the case where we have a non-String Object (this should
  // probably be handled upstream. At any rate, the following code should be
  // protected with assertions on the type of op1.
  typecast_exprt tcast(op1, to_pointer_type(op0.type()));
  dereference_exprt deref1(tcast, to_pointer_type(op0.type()).subtype());
  process_single_operand(ops, deref1, loc, symbol_table, init_code);
  return ops;
}

/// Finds the type of the data component
/// \param type: a type containing a "data" component
/// \param symbol_table: symbol table
/// \return type of the "data" component
typet java_string_library_preprocesst::get_data_type(
  const typet &type, const symbol_tablet &symbol_table)
{
  if(type.id()==ID_symbol)
  {
    symbolt sym=symbol_table.lookup(to_symbol_type(type).get_identifier());
    assert(sym.type.id()!=ID_symbol);
    return get_data_type(sym.type, symbol_table);
  }
  else
  {
    assert(type.id()==ID_struct);
    const struct_typet &struct_type=to_struct_type(type);
    for(auto component : struct_type.components())
      if(component.get_name()=="data")
        return component.type();
    assert(false && "type does not contain data component");
  }
}

/// Finds the type of the length component
/// \param type: a type containing a "length" component
/// \param symbol_table: symbol table
/// \return type of the "length" component
typet java_string_library_preprocesst::get_length_type(
  const typet &type, const symbol_tablet &symbol_table)
{
  if(type.id()==ID_symbol)
  {
    symbolt sym=symbol_table.lookup(to_symbol_type(type).get_identifier());
    assert(sym.type.id()!=ID_symbol);
    return get_length_type(sym.type, symbol_table);
  }
  else
  {
    assert(type.id()==ID_struct);
    const struct_typet &struct_type=to_struct_type(type);
    for(auto component : struct_type.components())
      if(component.get_name()=="length")
        return component.type();
    assert(false && "type does not contain length component");
  }
}

/// access length member
/// \param expr: an expression of structured type with length component
/// \param symbol_table: symbol table
/// \return expression representing the "length" member
exprt java_string_library_preprocesst::get_length(
  const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(
    expr, "length", get_length_type(expr.type(), symbol_table));
}

/// access data member
/// \param expr: an expression of structured type with length component
/// \param symbol_table: symbol table
/// \return expression representing the "data" member
exprt java_string_library_preprocesst::get_data(
  const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(expr, "data", get_data_type(expr.type(), symbol_table));
}

/// we declare a new `cprover_string` whose contents is deduced from the char
/// array.
/// \param array_pointer: an expression of type char array pointer
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \param code: code block, in which some assignments will be added
/// \return a string expression
string_exprt java_string_library_preprocesst::replace_char_array(
  const exprt &array_pointer,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &code)
{
  refined_string_typet ref_type=refined_string_type;
  dereference_exprt array(array_pointer, array_pointer.type().subtype());
  exprt array_data=get_data(array, symbol_table);
  // `deref_array` is *(array_pointer->data)`
  const typet &content_type=ref_type.get_content_type();
  dereference_exprt deref_array(array_data, array_data.type().subtype());

  // lhs_deref <- convert_pointer_to_char_array(*(array_pointer->data))
  symbolt sym_char_array=get_fresh_aux_symbol(
    content_type, "char_array", "char_array", loc, ID_java, symbol_table);
  symbol_exprt char_array=sym_char_array.symbol_expr();
  code.add(code_assign_function_application(
    char_array,
    ID_cprover_string_array_of_char_pointer_func,
    {deref_array},
    symbol_table));

  // string_expr is `{ rhs->length; string_array }`
  string_exprt string_expr(
    get_length(array, symbol_table), char_array, refined_string_type);
  // string_expr_sym <- { rhs->length; string_array }
  symbol_exprt string_expr_sym=
    fresh_string(refined_string_type, loc, symbol_table);
  code.add(code_assignt(string_expr_sym, string_expr));

  return string_expr;
}

/// add a symbol with static lifetime and name containing `cprover_string` and
/// given type
/// \param type: a type for refined strings
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \return a new symbol
symbol_exprt java_string_library_preprocesst::fresh_string(
  const typet &type, const source_locationt &loc, symbol_tablet &symbol_table)
{
  symbolt string_symbol=get_fresh_aux_symbol(
    type, "cprover_string", "cprover_string", loc, ID_java, symbol_table);
  string_symbol.is_static_lifetime=true;
  return string_symbol.symbol_expr();
}

/// add symbols with prefix cprover_string_length and cprover_string_data and
/// construct a string_expr from them.
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \param code: code block to which allocation instruction will be added
/// \return a new string_expr
string_exprt java_string_library_preprocesst::fresh_string_expr(
  const source_locationt &loc, symbol_tablet &symbol_table, code_blockt &code)
{
  refined_string_typet type=refined_string_type;
  symbolt sym_length=get_fresh_aux_symbol(
    type.get_index_type(),
    "cprover_string_length",
    "cprover_string_length",
    loc,
    ID_java,
    symbol_table);
  symbol_exprt length_field=sym_length.symbol_expr();
  symbol_exprt content_field=fresh_array(
    type.get_content_type(), loc, symbol_table);
  string_exprt str(length_field, content_field, type);
  code.add(code_declt(length_field));
  code.add(code_declt(content_field));
  return str;
}

/// add symbols with prefix cprover_string_length and cprover_string_data and
/// construct a string_expr from them.
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \param code: code block to which allocation instruction will be added
/// \return a new expression of refined string type
exprt java_string_library_preprocesst::fresh_string_expr_symbol(
  const source_locationt &loc, symbol_tablet &symbol_table, code_blockt &code)
{
  symbolt sym=get_fresh_aux_symbol(
    refined_string_type,
    "cprover_string",
    "cprover_string",
    loc,
    ID_java,
    symbol_table);
  code.add(code_declt(sym.symbol_expr()));
  return sym.symbol_expr();
}

/// declare a new String and allocate it
/// \param type: a type for string
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \param code: code block to which allocation instruction will be added
/// \return a new string
exprt java_string_library_preprocesst::allocate_fresh_string(
  const typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &code)
{
  exprt str=fresh_string(type, loc, symbol_table);
  code.add(code_declt(str));
  (void) allocate_dynamic_object_with_decl(
    str, str.type().subtype(), symbol_table, loc, code, false);
  return str;
}

/// declare a new character array and allocate it
/// \param type: a type for string
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \param code: code block to which allocation instruction will be added
/// \return a new array
exprt java_string_library_preprocesst::allocate_fresh_array(
  const typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &code)
{
  exprt array=fresh_array(type, loc, symbol_table);
  code.add(code_declt(array));
  (void) allocate_dynamic_object_with_decl(
    array, array.type().subtype(), symbol_table, loc, code, false);
  return array;
}

/// \param function_name: the name of the function
/// \param arguments: a list of arguments
/// \param type: return type of the function
/// \param symbol_table: a symbol table
/// \return a function application representing: `function_name(arguments)`
exprt java_string_library_preprocesst::make_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &type,
  symbol_tablet &symbol_table)
{
  // Names of function to call
  std::string fun_name=id2string(function_name);

  // Declaring the function
  declare_function(fun_name, type, symbol_table);

  // Function application
  function_application_exprt call(symbol_exprt(fun_name), type);
  call.arguments()=arguments;
  return call;
}

/// assign the result of a function call
/// \param lhs: an expression
/// \param function_name: the name of the function
/// \param arguments: a list of arguments
/// \param symbol_table: a symbol table
/// \return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = <function_name>(arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_function_application(
  const exprt &lhs,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  symbol_tablet &symbol_table)
{
  exprt fun_app=make_function_application(
    function_name, arguments, lhs.type(), symbol_table);
  return code_assignt(lhs, fun_app);
}

/// return the result of a function call
/// \param function_name: the name of the function
/// \param arguments: a list of arguments
/// \param type: the return type
/// \param symbol_table: a symbol table
/// \return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// return <function_name>(arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_return_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &type,
  symbol_tablet &symbol_table)
{
  exprt fun_app=make_function_application(
    function_name, arguments, type, symbol_table);
  return code_returnt(fun_app);
}

/// \param string_expr: a string expression
/// \param function_name: the name of the function
/// \param arguments: arguments of the function
/// \param symbol_table: symbol table
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// str.length = <function_name>_length(arguments)
/// str.data = <function_name>_data(arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_function_to_string_expr(
  const string_exprt &string_expr,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  symbol_tablet &symbol_table)
{
  // Names of function to call
  std::string fun_name_length=id2string(function_name)+"_length";
  std::string fun_name_data=id2string(function_name)+"_data";

  // Assignments
  codet assign_fun_length=code_assign_function_application(
    string_expr.length(), fun_name_length, arguments, symbol_table);
  codet assign_fun_data=code_assign_function_application(
    string_expr.content(), fun_name_data, arguments, symbol_table);

  return code_blockt({assign_fun_length, assign_fun_data});
}

/// \param function_name: the name of the function
/// \param arguments: arguments of the function
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \param code: code block in which we add instructions
/// \return return a string expr str and add the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// array = str.data
/// str.length = <function_name>_length(arguments)
/// str.data = <function_name>_data(arguments)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
string_exprt java_string_library_preprocesst::
  string_expr_of_function_application(
    const irep_idt &function_name,
    const exprt::operandst &arguments,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code)
{
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);
  code.add(code_assign_function_to_string_expr(
    string_expr, function_name, arguments, symbol_table));
  return string_expr;
}

/// Produce code for an assignment of a string expr to a Java string.
/// \param lhs: expression representing the java string to assign to
/// \param rhs_array: pointer to the array to assign
/// \param rhs_length: length of the array to assign
/// \param symbol_table: symbol table
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = { {Object}, length=rhs_length, data=rhs_array }
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_components_to_java_string(
  const exprt &lhs,
  const exprt &rhs_array,
  const exprt &rhs_length,
  symbol_tablet &symbol_table)
{
  assert(implements_java_char_sequence(lhs.type()));
  dereference_exprt deref(lhs, lhs.type().subtype());

  code_blockt code;

  // A String has a field Object with @clsid = String and @lock = false:
  const symbolt &jlo_symbol=symbol_table.lookup("java::java.lang.Object");
  const struct_typet &jlo_struct=to_struct_type(jlo_symbol.type);
  struct_exprt jlo_init(jlo_struct);
  jlo_init.copy_to_operands(constant_exprt(
    "java::java.lang.String", jlo_struct.components()[0].type()));
  jlo_init.copy_to_operands(from_integer(0, jlo_struct.components()[1].type()));

  struct_exprt struct_rhs(deref.type());
  struct_rhs.copy_to_operands(jlo_init);
  struct_rhs.copy_to_operands(rhs_length);
  struct_rhs.copy_to_operands(rhs_array);
  code.add(code_assignt(
    dereference_exprt(lhs, lhs.type().subtype()), struct_rhs));

  return code;
}

/// Produce code for an assignemnt of a string expr to a Java string.
/// \param lhs: an expression representing a java string
/// \param rhs: a string expression
/// \param symbol_table: symbol table
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = { {Object}, length=rhs.length, data=rhs.data }
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_string_expr_to_java_string(
  const exprt &lhs,
  const string_exprt &rhs,
  symbol_tablet &symbol_table)
{
  return code_assign_components_to_java_string(
    lhs, address_of_exprt(rhs.content()), rhs.length(), symbol_table);
}

/// Produce code for an assignment of a string from a string expr.
/// \param lhs: an expression representing a java string
/// \param rhs: a string expression
/// \param loc: a location in the program
/// \param symbol_table: symbol table
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// data = new array[];
/// *data = rhs.data;
/// lhs = { {Object} , length=rhs.length, data=data}
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::
  code_assign_string_expr_to_new_java_string(
    const exprt &lhs,
    const string_exprt &rhs,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  assert(implements_java_char_sequence(lhs.type()));
  dereference_exprt deref(lhs, lhs.type().subtype());

  code_blockt code;
  exprt new_array=allocate_fresh_array(
    get_data_type(deref.type(), symbol_table), loc, symbol_table, code);
  code.add(code_assignt(
    dereference_exprt(new_array, new_array.type().subtype()), rhs.content()));

  code.add(code_assign_components_to_java_string(
    lhs, new_array, rhs.length(), symbol_table));

  return code;
}

/// \param lhs: a string expression
/// \param rhs: an expression representing a java string
/// \param symbol_table: symbol table
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~
/// lhs.length=rhs->length
/// lhs.data=*(rhs->data)
/// ~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::code_assign_java_string_to_string_expr(
  const string_exprt &lhs, const exprt &rhs, symbol_tablet &symbol_table)
{
  assert(implements_java_char_sequence(rhs.type()));

  typet deref_type;
  if(rhs.type().subtype().id()==ID_symbol)
    deref_type=symbol_table.lookup(
      to_symbol_type(rhs.type().subtype()).get_identifier()).type;
  else
    deref_type=rhs.type().subtype();

  dereference_exprt deref(rhs, deref_type);

  // Fields of the string object
  exprt rhs_length=get_length(deref, symbol_table);
  exprt member_data=get_data(deref, symbol_table);
  dereference_exprt rhs_data(member_data, member_data.type().subtype());

  // Assignments
  code_blockt code;
  code.add(code_assignt(lhs.length(), rhs_length));

  // We always assume data of a String is not null
  not_exprt data_not_null(equal_exprt(
    member_data, null_pointer_exprt(to_pointer_type(member_data.type()))));
  code.add(code_assumet(data_not_null));
  code.add(code_assignt(lhs.content(), rhs_data));
  return code;
}

/// \param lhs: an expression representing a java string
/// \param s: the literal to be assigned
/// \param symbol_table: symbol table
/// \return return the following code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// tmp_string = "<s>"
/// lhs = (string_expr) tmp_string
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::
  code_assign_string_literal_to_string_expr(
    const string_exprt &lhs,
    const std::string &s,
    symbol_tablet &symbol_table)
{
  constant_exprt expr(s, string_typet());
  return code_assign_function_to_string_expr(
    lhs, ID_cprover_string_literal_func, {expr}, symbol_table);
}

/// Used to provide code for the Java String.equals(Object) function.
/// \param type: type of the function call
/// \param loc: location in the program_invocation_name
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr1 = {this->length; *this->data}
/// string_expr2 = {arg->length; *arg->data}
/// return cprover_string_equal(string_expr1, string_expr2)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_equals_function_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // TODO: Code should return false if Object is not String.
  code_blockt code;
  exprt::operandst ops;
  for(const auto &p : type.parameters())
  {
    symbol_exprt sym(p.get_identifier(), p.type());
    ops.push_back(sym);
  }
  exprt::operandst args=process_equals_function_operands(
    ops, loc, symbol_table, code);
  code.add(code_return_function_application(
    ID_cprover_string_equal_func, args, type.return_type(), symbol_table));
  return code;
}

/// Provide code for the String.valueOf(F) function.
/// \param type: type of the function call
/// \param loc: location in the program_invocation_name
/// \param symbol_table: symbol table
/// \return Code corresponding to the Java conversion of floats to strings.
codet java_string_library_preprocesst::make_float_to_string_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Getting the argument
  code_typet::parameterst params=type.parameters();
  assert(params.size()==1 && "wrong number of parameters in Float.toString");
  exprt arg=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Holder for output code
  code_blockt code;

  // Declaring and allocating String * str
  exprt str=allocate_fresh_string(type.return_type(), loc, symbol_table, code);

  // Expression representing 0.0
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  ieee_floatt zero_float(float_spec);
  zero_float.from_float(0.0);
  constant_exprt zero=zero_float.to_expr();

  // For each possible case with have a condition and a string_exprt
  std::vector<exprt> condition_list;
  std::vector<string_exprt> string_expr_list;

  // Case of computerized scientific notation
  condition_list.push_back(binary_relation_exprt(arg, ID_ge, zero));
  string_exprt sci_notation=fresh_string_expr(loc, symbol_table, code);
  exprt sci_notation_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assign_function_to_string_expr(
    sci_notation,
    ID_cprover_string_of_float_scientific_notation_func,
    {arg},
    symbol_table));
  // Assign string_expr_sym = { string_expr_length, string_expr_content }
  code.add(code_assignt(sci_notation_sym, sci_notation));
  string_expr_list.push_back(sci_notation);

  // Subcase of negative scientific notation
  condition_list.push_back(binary_relation_exprt(arg, ID_lt, zero));
  string_exprt neg_sci_notation=fresh_string_expr(loc, symbol_table, code);
  exprt neg_sci_notation_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  string_exprt minus_sign=fresh_string_expr(loc, symbol_table, code);
  code.add(code_assign_string_literal_to_string_expr(
    minus_sign, "-", symbol_table));
  code.add(code_assign_function_to_string_expr(
    neg_sci_notation,
    ID_cprover_string_concat_func,
    {minus_sign, sci_notation},
    symbol_table));
  code.add(code_assignt(neg_sci_notation_sym, neg_sci_notation));
  string_expr_list.push_back(neg_sci_notation);

  // Case of NaN
  condition_list.push_back(isnan_exprt(arg));
  string_exprt nan=fresh_string_expr(loc, symbol_table, code);
  code.add(code_assign_string_literal_to_string_expr(
    nan, "NaN", symbol_table));
  string_expr_list.push_back(nan);

  // Case of Infinity
  extractbit_exprt is_neg(arg, float_spec.width()-1);
  condition_list.push_back(and_exprt(isinf_exprt(arg), not_exprt(is_neg)));
  string_exprt infinity=fresh_string_expr(loc, symbol_table, code);
  code.add(code_assign_string_literal_to_string_expr(
    infinity, "Infinity", symbol_table));
  string_expr_list.push_back(infinity);

  // Case -Infinity
  string_exprt minus_infinity=fresh_string_expr(loc, symbol_table, code);
  condition_list.push_back(and_exprt(isinf_exprt(arg), is_neg));
  code.add(code_assign_string_literal_to_string_expr(
    minus_infinity, "-Infinity", symbol_table));
  string_expr_list.push_back(minus_infinity);

  // Case of simple notation
  ieee_floatt bound_inf_float(float_spec);
  ieee_floatt bound_sup_float(float_spec);
  bound_inf_float.from_float(1e-3);
  bound_sup_float.from_float(1e7);
  bound_inf_float.change_spec(float_spec);
  bound_sup_float.change_spec(float_spec);
  constant_exprt bound_inf=bound_inf_float.to_expr();
  constant_exprt bound_sup=bound_sup_float.to_expr();

  and_exprt is_simple_float(
    binary_relation_exprt(arg, ID_ge, bound_inf),
    binary_relation_exprt(arg, ID_lt, bound_sup));
  condition_list.push_back(is_simple_float);

  string_exprt simple_notation=fresh_string_expr(loc, symbol_table, code);
  exprt simple_notation_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assign_function_to_string_expr(
    simple_notation, ID_cprover_string_of_float_func, {arg}, symbol_table));
  code.add(code_assignt(simple_notation_sym, simple_notation));
  string_expr_list.push_back(simple_notation);

  // Case of a negative number in simple notation
  and_exprt is_neg_simple_float(
    binary_relation_exprt(arg, ID_le, unary_minus_exprt(bound_inf)),
    binary_relation_exprt(arg, ID_gt, unary_minus_exprt(bound_sup)));
  condition_list.push_back(is_neg_simple_float);

  string_exprt neg_simple_notation=fresh_string_expr(loc, symbol_table, code);
  exprt neg_simple_notation_sym=
    fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assign_function_to_string_expr(
    neg_simple_notation,
    ID_cprover_string_concat_func,
    {minus_sign, simple_notation},
    symbol_table));
  code.add(code_assignt(neg_simple_notation_sym, simple_notation));
  string_expr_list.push_back(neg_simple_notation);

  // Combining all cases
  assert(string_expr_list.size()==condition_list.size());
  // We do not check the condition of the first element in the list as it
  // will be reached only if all other conditions are not satisfied.
  codet tmp_code=code_assign_string_expr_to_java_string(
    str, string_expr_list[0], symbol_table);
  for(std::size_t i=1; i<condition_list.size(); i++)
  {
    code_ifthenelset ife;
    ife.cond()=condition_list[i];
    ife.then_case()=code_assign_string_expr_to_new_java_string(
      str, string_expr_list[i], loc, symbol_table);
    ife.else_case()=tmp_code;
    tmp_code=ife;
  }
  code.add(tmp_code);

  // Return str
  code.add(code_returnt(str));
  return code;
}

/// Generate the goto code for string initialization.
/// \param function_name: name of the function to be called
/// \param type: the type of the function call
/// \param loc: location in program
/// \param symbol_table: the symbol table to populate
/// \param ignore_first_arg: boolean flag telling that the first argument should
///   not be part of the arguments of the call (but only used to be assigned the
///   result)
/// \return code for the String.<init>(args) function:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// cprover_string_length = fun(arg).length;
/// cprover_string_array = fun(arg).data;
/// this->length = cprover_string_length;
/// this->data = cprover_string_array;
/// cprover_string = {.=cprover_string_length, .=cprover_string_array};
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_init_function_from_call(
  const irep_idt &function_name,
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  bool ignore_first_arg)
{
  code_typet::parameterst params=type.parameters();

  // The first parameter is the object to be initialized
  assert(!params.empty());
  exprt arg_this=symbol_exprt(params[0].get_identifier(), params[0].type());
  if(ignore_first_arg)
    params.erase(params.begin());

  // Holder for output code
  code_blockt code;

  // Processing parameters
  exprt::operandst args=process_parameters(params, loc, symbol_table, code);

  // string_expr <- function(arg1)
  string_exprt string_expr=string_expr_of_function_application(
    function_name, args, loc, symbol_table, code);

  // arg_this <- string_expr
  code.add(code_assign_string_expr_to_new_java_string(
    arg_this, string_expr, loc, symbol_table));

  // string_expr_sym <- {string_expr.length, string_expr.content}
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));

  return code;
}

/// Call a cprover internal function, assign the result to object `this` and
/// return it.
/// \param function_name: name of the function to be called
/// \param type: the type of the function call
/// \param loc: location in program
/// \param symbol_table: the symbol table to populate
/// \return Code calling function with the given function name.
codet java_string_library_preprocesst::
  make_assign_and_return_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  // This is similar to assign functions except we return a pointer to `this`
  code_blockt code;
  code.add(make_assign_function_from_call(
    function_name, type, loc, symbol_table));
  code_typet::parameterst params=type.parameters();
  assert(!params.empty());
  exprt arg_this=symbol_exprt(params[0].get_identifier(), params[0].type());
  code.add(code_returnt(arg_this));
  return code;
}

/// Call a cprover internal function and assign the result to object `this`.
/// \param function_name: name of the function to be called
/// \param type: the type of the function call
/// \param loc: location in program
/// \param symbol_table: the symbol table to populate
/// \return Code assigning result of a call to the function with given function
///   name.
codet java_string_library_preprocesst::make_assign_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  // This is similar to initialization function except we do not ignore
  // the first argument
  codet code=make_init_function_from_call(
    function_name, type, loc, symbol_table, false);
  return code;
}

/// Used to provide our own implementation of the
/// `java.lang.String.toCharArray:()[C` function.
/// \param type: type of the function called
/// \param loc: location in the source
/// \param symbol_table: the symbol table
/// \return Code corresponding to
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// lhs = new java::array[char]
/// string_expr = {length=this->length, content=*(this->data)}
/// data = new char[]
/// *data = string_expr.content
/// lhs->data = &data[0]
/// lhs->length = string_expr.length
/// return lhs
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_string_to_char_array_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  code_blockt code;
  assert(!type.parameters().empty());
  const code_typet::parametert &p=type.parameters()[0];
  symbol_exprt string_argument(p.get_identifier(), p.type());
  assert(implements_java_char_sequence(string_argument.type()));

  // lhs = new java::array[char]
  exprt lhs=allocate_fresh_array(
    type.return_type(), loc, symbol_table, code);

  // string_expr = {this->length, this->data}
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);
  code.add(code_assign_java_string_to_string_expr(
    string_expr, string_argument, symbol_table));
  exprt string_expr_sym=fresh_string_expr_symbol(
    loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));

  // data = new char[]
  exprt data=allocate_fresh_array(
    pointer_typet(string_expr.content().type()), loc, symbol_table, code);

  // *data = string_expr.content
  dereference_exprt deref_data(data, data.type().subtype());
  code.add(code_assignt(deref_data, string_expr.content()));

  // lhs->data = &data[0]
  dereference_exprt deref_lhs(lhs, lhs.type().subtype());
  exprt lhs_data=get_data(deref_lhs, symbol_table);
  index_exprt first_elt(
    deref_data, from_integer(0, java_int_type()), java_char_type());
  code.add(code_assignt(lhs_data, address_of_exprt(first_elt)));

  // lhs->length = string_expr.length
  exprt lhs_length=get_length(deref_lhs, symbol_table);
  code.add(code_assignt(lhs_length, string_expr.length()));

  // return lhs
  code.add(code_returnt(lhs));
  return code;
}

/// Adds to the code an assignment of the form
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// type_name tmp_type_name
/// tmp_type_name = ((Classname*)arg_i)->value
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// and returns `tmp_typename`.
/// In case the class corresponding to `type_name` is not available in
/// `symbol_table`, the variable is declared but not assigned.
/// Used to access the values of the arguments of `String.format`.
/// \param object: an expression representing a reference to an object
/// \param type_name: name of the corresponding primitive type, this can be
///        one of the following: ID_boolean, ID_char, ID_byte, ID_short, ID_int,
///        ID_long, ID_float, ID_double, ID_void
/// \param loc: a location in the source
/// \param symbol_table: the symbol table
/// \param code: code block to which we are adding some assignments
/// \return An expression contaning a symbol `tmp_type_name` where `type_name`
///         is the given argument (ie. boolean, char etc.). Which represents the
///         primitive value contained in the given object.
exprt java_string_library_preprocesst::get_primitive_value_of_object(
  const exprt &object,
  irep_idt type_name,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &code)
{
  symbol_typet object_type;
  typet value_type;
  if(type_name==ID_boolean)
  {
    value_type=java_boolean_type();
    object_type=symbol_typet("java::java.lang.Boolean");
  }
  else if(type_name==ID_char)
  {
    value_type=java_char_type();
    object_type=symbol_typet("java::java.lang.Character");
  }
  else if(type_name==ID_byte)
  {
    value_type=java_byte_type();
    object_type=symbol_typet("java::java.lang.Byte");
  }
  else if(type_name==ID_short)
  {
    value_type=java_short_type();
    object_type=symbol_typet("java::java.lang.Short");
  }
  else if(type_name==ID_int)
  {
    value_type=java_int_type();
    object_type=symbol_typet("java::java.lang.Integer");
  }
  else if(type_name==ID_long)
  {
    value_type=java_long_type();
    object_type=symbol_typet("java::java.lang.Long");
  }
  else if(type_name==ID_float)
  {
    value_type=java_float_type();
    object_type=symbol_typet("java::java.lang.Float");
  }
  else if(type_name==ID_double)
  {
    value_type=java_double_type();
    object_type=symbol_typet("java::java.lang.Double");
  }
  else if(type_name==ID_void)
    return nil_exprt();
  else
    UNREACHABLE;

  // declare tmp_type_name to hold the value
  std::string aux_name="tmp_"+id2string(type_name);
  symbolt symbol=get_fresh_aux_symbol(
    value_type, aux_name, aux_name, loc, ID_java, symbol_table);
  exprt value=symbol.symbol_expr();

  // Check that the type of the object is in the symbol table,
  // otherwise there is no safe way of finding its value.
  if(symbol_table.has_symbol(object_type.get_identifier()))
  {
    struct_typet struct_type=to_struct_type(
      symbol_table.lookup(object_type.get_identifier()).type);
    // Check that the type has a value field
    const struct_union_typet::componentt value_comp=
      struct_type.get_component("value");
    if(!value_comp.is_nil())
    {
      pointer_typet pointer_type(struct_type);
      dereference_exprt deref(
        typecast_exprt(object, pointer_type), pointer_type.subtype());
      member_exprt deref_value(deref, value_comp.get_name(), value_comp.type());
      code.add(code_assignt(value, deref_value));
      return value;
    }
  }

  warning() << object_type.get_identifier()
            << " not available to format function" << eom;
  code.add(code_declt(value));
  return value;
}

/// Helper for format function. Returns the expression:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// *((void**)(argv->data)+index )
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// which corresponds to the object at position `index` in  `argv`.
/// \param argv: reference to an array of references
/// \param index: index of the desired object
/// \return An expression representing the object at position `index` of `argv`.
exprt java_string_library_preprocesst::get_object_at_index(
  const exprt &argv,
  int index)
{
  dereference_exprt deref_objs(argv, argv.type().subtype());
  pointer_typet empty_pointer((empty_typet()));
  pointer_typet pointer_of_pointer;
  pointer_of_pointer.copy_to_subtypes(empty_pointer);
  member_exprt data_member(deref_objs, "data", pointer_of_pointer);
  plus_exprt data_pointer_plus_index(
    data_member, from_integer(index, java_int_type()), data_member.type());
  dereference_exprt data_at_index(
    data_pointer_plus_index, data_pointer_plus_index.type().subtype());
  return data_at_index;
}

/// Helper for format function. Adds code:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr arg_i_string_expr;
/// int tmp_int;
/// float tmp_float;
/// char tmp_char;
/// boolean tmp_boolean;
/// Object* arg_i=get_object_at_index(argv, index)
/// if(arg_i!=NULL)
/// {
///   if(arg_i.@class_identifier=="java::java.lang.String")
///   {
///     arg_i_string_expr = (string_expr)((String*)arg_i_as_string)
///   }
///   tmp_int=((Integer)arg_i)->value
///   tmp_float=((Float)arg_i)->value
///   tmp_char=((Char)arg_i)->value
///   tmp_boolean=((Boolean)arg_i)->value
/// }
/// arg_i_struct = { string_expr=arg_i_string_expr;
///   integer=tmp_int; float=tmp_float; char=tmp_char; boolean=tmp_boolean}
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// and returns `arg_i_struct`.
///
/// TODO: date_time and hash code are not implemented
/// \param argv: reference to an array of references
/// \param index: index of the desired argument
/// \param structured_type: type for arguments of the internal format function
/// \param loc: a location in the source
/// \param symbol_table: the symbol table
/// \param code: code block to which we are adding some assignments
/// \return An expression of type `structured_type` representing the possible
///         values of the argument at position `index` of `argv`.
exprt java_string_library_preprocesst::make_argument_for_format(
  const exprt &argv,
  int index,
  const struct_typet &structured_type,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &code)
{
  // Declarations of the fields of arg_i_struct
  // arg_i_struct is { arg_i_string_expr, tmp_int, tmp_char, ... }
  struct_exprt arg_i_struct(structured_type);
  std::list<exprt> field_exprs;
  for(const auto & comp : structured_type.components())
  {
    const irep_idt &name=comp.get_name();
    const typet &type=comp.type();
    exprt field_expr;
    if(name!="string_expr")
    {
      std::string tmp_name="tmp_"+id2string(name);
      symbolt field_symbol=get_fresh_aux_symbol(
        type, tmp_name, tmp_name, loc, ID_java, symbol_table);
      field_expr=field_symbol.symbol_expr();
      code.add(code_declt(field_expr));
    }
    else
      field_expr=fresh_string_expr(loc, symbol_table, code);

    field_exprs.push_back(field_expr);
    arg_i_struct.copy_to_operands(field_expr);
  }

  // arg_i = argv[index]
  exprt obj=get_object_at_index(argv, index);
  symbolt object_symbol=get_fresh_aux_symbol(
    obj.type(), "tmp_object", "tmp_object", loc, ID_java, symbol_table);
  symbol_exprt arg_i=object_symbol.symbol_expr();
  (void) allocate_dynamic_object_with_decl(
    arg_i, obj.type(), symbol_table, loc, code, false);
  code.add(code_assignt(arg_i, obj));
  code.add(code_assumet(not_exprt(equal_exprt(
    arg_i, null_pointer_exprt(to_pointer_type(arg_i.type()))))));

  // if arg_i != null then [code_not_null]
  code_ifthenelset code_avoid_null_arg;
  code_avoid_null_arg.cond()=not_exprt(equal_exprt(
    arg_i, null_pointer_exprt(to_pointer_type(arg_i.type()))));
  code_blockt code_not_null;

  // Assigning all the fields of arg_i_struct
  for(const auto &comp : structured_type.components())
  {
    const irep_idt &name=comp.get_name();
    exprt field_expr=field_exprs.front();
    field_exprs.pop_front();

    if(name=="string_expr")
    {
      pointer_typet string_pointer(symbol_typet("java::java.lang.String"));
      typecast_exprt arg_i_as_string(arg_i, string_pointer);
      code_not_null.add(code_assign_java_string_to_string_expr(
        to_string_expr(field_expr), arg_i_as_string, symbol_table));
      exprt arg_i_string_expr_sym=fresh_string_expr_symbol(
        loc, symbol_table, code_not_null);
      code_not_null.add(code_assignt(
        arg_i_string_expr_sym, to_string_expr(field_expr)));
    }
    else if(name==ID_int || name==ID_float || name==ID_char || name==ID_boolean)
    {
      exprt value=get_primitive_value_of_object(
        arg_i, name, loc, symbol_table, code_not_null);
      code_not_null.add(code_assignt(field_expr, value));
    }
    else
    {
      // TODO: date_time and hash_code not implemented
    }
  }

  code.add(code_not_null);
  return arg_i_struct;
}

/// Used to provide code for the Java String.format function.
///
/// TODO: date_time and hash code are not implemented, and we set a limit of
/// 10 arguments
/// \param type: type of the function call
/// \param loc: location in the program_invocation_name
/// \param symbol_table: symbol table
/// \return Code implementing the Java String.format function.
///         Since the exact class of the arguments is not known, we give as
///         argument to the internal format function a structure containing
///         the different possible types.
codet java_string_library_preprocesst::make_string_format_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  PRECONDITION(type.parameters().size()==2);
  code_blockt code;
  exprt::operandst args=process_parameters(
    type.parameters(), loc, symbol_table, code);
  INVARIANT(args.size()==2, "String.format should have two arguments");

  // The argument can be:
  // a string, an integer, a floating point, a character, a boolean,
  // an object of which we take the hash code, or a date/time
  struct_typet structured_type;
  structured_type.components().emplace_back("string_expr", refined_string_type);
  structured_type.components().emplace_back(ID_int, java_int_type());
  structured_type.components().emplace_back(ID_float, java_float_type());
  structured_type.components().emplace_back(ID_char, java_char_type());
  structured_type.components().emplace_back(ID_boolean, java_boolean_type());
  // TODO: hash_code not implemented for now
  structured_type.components().emplace_back("hashcode", java_int_type());
  // TODO: date_time type not implemented for now
  structured_type.components().emplace_back("date_time", java_int_type());

  // We will process arguments so that each is converted to a `struct_exprt`
  // containing each possible type used in format specifiers.
  std::vector<exprt> processed_args;
  processed_args.push_back(args[0]);
  for(std::size_t i=0; i<MAX_FORMAT_ARGS; ++i)
    processed_args.push_back(make_argument_for_format(
      args[1], i, structured_type, loc, symbol_table, code));

  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);
  code.add(code_assign_function_to_string_expr(
    string_expr, ID_cprover_string_format_func, processed_args, symbol_table));
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));
  exprt java_string=allocate_fresh_string(
    type.return_type(), loc, symbol_table, code);
  code.add(code_assign_string_expr_to_new_java_string(
    java_string, string_expr, loc, symbol_table));
  code.add(code_returnt(java_string));
  return code;
}

/// Used to provide our own implementation of the java.lang.Object.getClass()
/// function.
/// \param type: type of the function called
/// \param loc: location in the source
/// \param symbol_table: the symbol table
/// \return Code corresponding to
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// Class class1;
/// string_expr1 = substr(this->@class_identifier, 6)
/// class1=Class.forName(string_expr1)
/// return class1
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_object_get_class_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  code_typet::parameterst params=type.parameters();
  exprt this_obj=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Code to be returned
  code_blockt code;

  // > Class class1;
  pointer_typet class_type(symbol_table.lookup("java::java.lang.Class").type);
  symbolt class1_sym=get_fresh_aux_symbol(
    class_type, "class_symbol", "class_symbol", loc, ID_java, symbol_table);
  symbol_exprt class1=class1_sym.symbol_expr();
  code.add(code_declt(class1));

  // class_identifier is this->@class_identifier
  member_exprt class_identifier(
    dereference_exprt(this_obj, this_obj.type().subtype()),
    "@class_identifier",
    string_typet());

  // string_expr = cprover_string_literal(this->@class_identifier)
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);
  code.add(
    code_assign_function_to_string_expr(
      string_expr,
      ID_cprover_string_literal_func,
      {class_identifier},
      symbol_table));
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));

  // string_expr1 = substr(string_expr, 6)
  // We do this to remove the "java::" prefix
  string_exprt string_expr1=fresh_string_expr(loc, symbol_table, code);
  code.add(
    code_assign_function_to_string_expr(
      string_expr1,
      ID_cprover_string_substring_func,
      {string_expr, from_integer(6, java_int_type())},
      symbol_table));
  exprt string_expr_sym1=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym1, string_expr1));

  // string1 = (String*) string_expr
  pointer_typet string_ptr_type(
    symbol_table.lookup("java::java.lang.String").type);
  exprt string1=allocate_fresh_string(string_ptr_type, loc, symbol_table, code);
  code.add(
    code_assign_string_expr_to_new_java_string(
      string1, string_expr1, loc, symbol_table));

  // > class1 = Class.forName(string1)
  code_function_callt fun_call;
  fun_call.function()=symbol_exprt(
    "java::java.lang.Class.forName:(Ljava/lang/String;)Ljava/lang/Class;");
  fun_call.lhs()=class1;
  fun_call.arguments().push_back(string1);
  code_typet fun_type;
  fun_type.return_type()=string1.type();
  fun_call.function().type()=fun_type;
  code.add(fun_call);

  // > return class1;
  code.add(code_returnt(class1));
  return code;
}

/// Provide code for a function that calls a function from the solver and simply
/// returns it.
/// \param function_name: name of the function to be called
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~
/// return function_name(args)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_function_from_call(
  const irep_idt &function_name,
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_blockt code;
  exprt::operandst args=process_parameters(
    type.parameters(), loc, symbol_table, code);
  code.add(code_return_function_application(
    function_name, args, type.return_type(), symbol_table));
  return code;
}

/// Provide code for a function that calls a function from the solver and return
/// the string_expr result as a Java string.
/// \param function_name: name of the function to be called
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr = function_name(args)
/// string = new String
/// string = string_expr_to_string(string)
/// return string
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::
  make_string_returning_function_from_call(
    const irep_idt &function_name,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table)
{
  // Code for the output
  code_blockt code;

  // Calling the function
  exprt::operandst arguments=process_parameters(
    type.parameters(), loc, symbol_table, code);

  // String expression that will hold the result
  string_exprt string_expr=string_expr_of_function_application(
    function_name, arguments, loc, symbol_table, code);

  // Assign string_expr to symbol to keep track of it
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));

  // Assign to string
  exprt str=allocate_fresh_string(type.return_type(), loc, symbol_table, code);
  code.add(code_assign_string_expr_to_new_java_string(
    str, string_expr, loc, symbol_table));

  // Return value
  code.add(code_returnt(str));
  return code;
}

/// Generates code for a function which copies a string object to a new string
/// object.
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr = string_to_string_expr(arg0)
/// string_expr_sym = { string_expr.length; string_expr.content }
/// str = new String
/// str = string_expr_to_string(string_expr)
/// return str
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_copy_string_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Code for the output
  code_blockt code;

  // String expression that will hold the result
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);

  // Assign the argument to string_expr
  code_typet::parametert op=type.parameters()[0];
  symbol_exprt arg0(op.get_identifier(), op.type());
  code.add(code_assign_java_string_to_string_expr(
    string_expr, arg0, symbol_table));

  // Assign string_expr to string_expr_sym
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));

  // Allocate and assign the string
  exprt str=allocate_fresh_string(type.return_type(), loc, symbol_table, code);
  code.add(code_assign_string_expr_to_new_java_string(
    str, string_expr, loc, symbol_table));

  // Return value
  code.add(code_returnt(str));
  return code;
}

/// Generates code for a constructor of a string object from another string
/// object.
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// string_expr = java_string_to_string_expr(arg1)
/// string_expr_sym = { string_expr.length; string_expr.content }
/// this = string_expr_to_java_string(string_expr)
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_copy_constructor_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Code for the output
  code_blockt code;

  // String expression that will hold the result
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);

  // Assign argument to a string_expr
  code_typet::parameterst params=type.parameters();
  symbol_exprt arg1(params[1].get_identifier(), params[1].type());
  code.add(code_assign_java_string_to_string_expr(
    string_expr, arg1, symbol_table));

  // Assign string_expr to symbol to keep track of it
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(string_expr_sym, string_expr));

  // Assign string_expr to `this` object
  symbol_exprt arg_this(params[0].get_identifier(), params[0].type());
  code.add(code_assign_string_expr_to_new_java_string(
    arg_this, string_expr, loc, symbol_table));

  return code;
}

/// Generates code for the String.length method
/// \param type: type of the function
/// \param loc: location in the source
/// \param symbol_table: symbol table
/// \return Code corresponding to:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// str_expr = java_string_to_string_expr(this)
/// str_expr_sym = str_expr
/// return this->length
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
codet java_string_library_preprocesst::make_string_length_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Code for the output
  code_blockt code;

  code_typet::parameterst params=type.parameters();
  symbol_exprt arg_this(params[0].get_identifier(), params[0].type());
  dereference_exprt deref(arg_this, arg_this.type().subtype());

  // Create a new string_exprt to be picked up by the solver
  string_exprt str_expr=fresh_string_expr(loc, symbol_table, code);

  // Assign this to str_expr
  code.add(
    code_assign_java_string_to_string_expr(str_expr, arg_this, symbol_table));

  // Assign str_expr to str_expr_sym for that expression to be present in the
  // symbol table in order to be processed by the string solver
  exprt str_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);
  code.add(code_assignt(str_expr_sym, str_expr));
  code.add(code_returnt(get_length(deref, symbol_table)));

  return code;
}

/// Should be called to provide code for string functions that are used in the
/// code but for which no implementation is provided.
/// \param function_id: name of the function
/// \param type: its type
/// \param loc: location in the program
/// \param symbol_table: a symbol table
/// \return Code for the body of the String functions if they are part of the
///   supported String functions, nil_exprt otherwise.
exprt java_string_library_preprocesst::code_for_function(
  const irep_idt &function_id,
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
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
  if(it!=conversion_table.end())
    return it->second(type, loc, symbol_table);

  return nil_exprt();
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

/// fill maps with correspondence from java method names to conversion functions
void java_string_library_preprocesst::initialize_conversion_table()
{
  character_preprocess.initialize_conversion_table();

  string_types=
    std::unordered_set<irep_idt, irep_id_hash>{"java.lang.String",
                                               "java.lang.StringBuilder",
                                               "java.lang.CharSequence",
                                               "java.lang.StringBuffer"};

  // The following list of function is organized by libraries, with
  // constructors first and then methods in alphabetic order.
  // Methods that are not supported here should ultimately have Java models
  // provided for them in the class-path.

  // String library
  conversion_table
    ["java::java.lang.String.<init>:(Ljava/lang/String;)V"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_constructor_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  conversion_table
    ["java::java.lang.String.<init>:(Ljava/lang/StringBuilder;)V"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_constructor_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_constructor
    ["java::java.lang.String.<init>:([C)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_constructor
    ["java::java.lang.String.<init>:([CII)V"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_constructor
    ["java::java.lang.String.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_function
    ["java::java.lang.String.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.compareTo:(Ljava/lang/String;)I"]=
      ID_cprover_string_compare_to_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.concat:(Ljava/lang/String;)Ljava/lang/String;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z"]=
    ID_cprover_string_contains_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.copyValueOf:([CII)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.copyValueOf:([C)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.endsWith:(Ljava/lang/String;)Z"]=
      ID_cprover_string_endswith_func;

  conversion_table["java::java.lang.String.equals:(Ljava/lang/Object;)Z"]=
    std::bind(
      &java_string_library_preprocesst::make_equals_function_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3);
  cprover_equivalent_to_java_function
    ["java::java.lang.String.equalsIgnoreCase:(Ljava/lang/String;)Z"]=
      ID_cprover_string_equals_ignore_case_func;
  conversion_table
    ["java::java.lang.String.format:(Ljava/lang/String;[Ljava/lang/Object;)"
      "Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_string_format_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_function
    ["java::java.lang.String.hashCode:()I"]=
      ID_cprover_string_hash_code_func;
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
    ["java::java.lang.String.intern:()Ljava/lang/String;"]=
      ID_cprover_string_intern_func;
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
  conversion_table
    ["java::java.lang.String.length:()I"]=
      std::bind(
        &java_string_library_preprocesst::make_string_length_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_function
    ["java::java.lang.String.offsetByCodePoints:(II)I"]=
      ID_cprover_string_offset_by_code_point_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.replace:(CC)Ljava/lang/String;"]=
      ID_cprover_string_replace_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.startsWith:(Ljava/lang/String;)Z"]=
      ID_cprover_string_startswith_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.String.startsWith:(Ljava/lang/String;I)Z"]=
      ID_cprover_string_startswith_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.subSequence:(II)Ljava/lang/CharSequence;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  conversion_table
    ["java::java.lang.String.toCharArray:()[C"]=
      std::bind(
        &java_string_library_preprocesst::make_string_to_char_array_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.toLowerCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_lower_case_func;
  conversion_table
    ["java::java.lang.String.toString:()Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.toUpperCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_upper_case_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.trim:()Ljava/lang/String;"]=
      ID_cprover_string_trim_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(Z)Ljava/lang/String;"]=
      ID_cprover_string_of_bool_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(C)Ljava/lang/String;"]=
      ID_cprover_string_of_char_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:([C)Ljava/lang/String;"]=
      ID_cprover_string_copy_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:([CII)Ljava/lang/String;"]=
      ID_cprover_string_copy_func;
  conversion_table
    ["java::java.lang.String.valueOf:(D)Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_float_to_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  conversion_table
    ["java::java.lang.String.valueOf:(F)Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_float_to_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(J)Ljava/lang/String;"]=
      ID_cprover_string_of_long_func;

  // StringBuilder library
  conversion_table
    ["java::java.lang.StringBuilder.<init>:(Ljava/lang/String;)V"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_constructor_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_constructor
    ["java::java.lang.StringBuilder.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:([C)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(D)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_double_func;
  cprover_equivalent_to_java_assign_and_return_function
      ["java::java.lang.StringBuilder.append:(Ljava/lang/CharSequence;II)"
        "Ljava/lang/StringBuilder;"]=
        ID_cprover_string_concat_func;
    cprover_equivalent_to_java_assign_and_return_function
      ["java::java.lang.StringBuilder.append:(Ljava/lang/CharSequence;)"
        "Ljava/lang/StringBuilder;"]=
        ID_cprover_string_concat_func;
    cprover_equivalent_to_java_assign_and_return_function
      ["java::java.lang.StringBuilder.append:(Ljava/lang/String;)"
        "Ljava/lang/StringBuilder;"]=
        ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Z)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_bool_func;
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
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.delete:(II)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_delete_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.deleteCharAt:(I)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_delete_char_at_func;
  cprover_equivalent_to_java_assign_and_return_function
      ["java::java.lang.StringBuilder.insert:(IC)Ljava/lang/StringBuilder;"]=
        ID_cprover_string_insert_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(I[C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(I[CII)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IZ)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(II)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IJ)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_long_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  conversion_table
    ["java::java.lang.StringBuilder.length:()I"]=
      std::bind(
        &java_string_library_preprocesst::make_string_length_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuilder.setCharAt:(IC)V"]=
      ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuilder.setLength:(I)V"]=
      ID_cprover_string_set_length_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuilder.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuilder.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  conversion_table
    ["java::java.lang.StringBuilder.toString:()Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);

  // StringBuffer library
  conversion_table
    ["java::java.lang.StringBuffer.<init>:(Ljava/lang/String;)V"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_constructor_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_constructor
    ["java::java.lang.StringBuffer.<init>:()V"]=
      ID_cprover_string_empty_string_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:([C)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(D)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_double_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(F)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_float_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(I)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(J)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_long_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Z)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.appendCodePoint:(I)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_code_point_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointAt:(I)I"]=
      ID_cprover_string_code_point_at_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointBefore:(I)I"]=
      ID_cprover_string_code_point_before_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.codePointCount:(II)I"]=
      ID_cprover_string_code_point_count_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.delete:(II)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_delete_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.deleteCharAt:(I)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_delete_char_at_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IC)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(I[C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(I[CII)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(II)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IJ)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_long_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IZ)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_bool_func;
  conversion_table
    ["java::java.lang.StringBuffer.length:()I"]=
      conversion_table["java::java.lang.String.length:()I"];
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuffer.setCharAt:(IC)V"]=
      ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuffer.setLength:(I)V"]=
    ID_cprover_string_set_length_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuffer.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuffer.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  conversion_table
    ["java::java.lang.StringBuffer.toString:()Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);

  // CharSequence library
  cprover_equivalent_to_java_function
    ["java::java.lang.CharSequence.charAt:(I)C"]=
      ID_cprover_string_char_at_func;
  conversion_table
    ["java::java.lang.CharSequence.toString:()Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  conversion_table
    ["java::java.lang.CharSequence.length:()I"]=
      conversion_table["java::java.lang.String.length:()I"];

  // Other libraries
  conversion_table
    ["java::java.lang.Float.toString:(F)Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_float_to_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_function
    ["java::java.lang.Integer.parseInt:(Ljava/lang/String;)I"]=
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.Integer.parseInt:(Ljava/lang/String;I)I"]=
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.Long.parseLong:(Ljava/lang/String;)J"]=
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.Long.parseLong:(Ljava/lang/String;I)J"]=
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.Integer.toHexString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_hex_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.Integer.toString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_func;
  conversion_table
    ["java::java.lang.Object.getClass:()Ljava/lang/Class;"]=
      std::bind(
        &java_string_library_preprocesst::make_object_get_class_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
}
