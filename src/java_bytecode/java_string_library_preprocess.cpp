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

/*******************************************************************\

Function: java_string_library_preprocesst::java_type_matches_tag

  Inputs:
    type - a type
    tag - a string

  Output: Boolean telling whether the type is a struct with the given
          tag or a symbolic type with the tag prefixed by "java::"

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_pointer_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java string pointer

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java string

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.String");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_builder_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java StringBuilder

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_builder_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.StringBuilder");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_builder_pointer_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java StringBuilder
          pointers

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_buffer_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java StringBuffer

\*******************************************************************/

bool java_string_library_preprocesst::is_java_string_buffer_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.StringBuffer");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_string_buffer_pointer_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java StringBuffer
          pointers

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_sequence_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java char sequence

\*******************************************************************/

bool java_string_library_preprocesst::is_java_char_sequence_type(
  const typet &type)
{
  return java_type_matches_tag(type, "java.lang.CharSequence");
}

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_sequence_pointer_type

  Inputs: a type

  Output: Boolean telling whether the type is that of a pointer
          to a java char sequence

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::is_java_char_array_type

  Inputs: a type

  Output: Boolean telling whether the type is that of java char array

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::string_data_type

  Inputs:
    symbol_table - a symbol_table containing an entry for java Strings

  Output: the type of data fields in java Strings.

\*******************************************************************/

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

/*******************************************************************\

Function: string_refine_preprocesst::process_arguments

  Inputs:
    params - a list of function parameters
    loc - location in the source
    symbol_table - symbol table
    init_code - code block, in which declaration of some arguments
                may be added

  Output: a list of expressions

 Purpose: calls string_refine_preprocesst::process_operands with a
          list of parameters.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::process_operands

  Inputs:
    operands - a list of expressions
    loc - location in the source
    symbol_table - symbol table
    init_code - code block, in which declaration of some arguments
                may be added

  Output: a list of expressions

 Purpose: for each expression that is of a type implementing strings,
          we declare a new `cprover_string` whose contents is deduced
          from the expression and replace the
          expression by this cprover_string in the output list;
          in the other case the expression is kept as is for the output list.
          Also does the same thing for char array references.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::process_equals_function_operands

  Inputs:
    operands - a list of expressions
    loc - location in the source
    symbol_table - symbol table
    init_code - code block, in which declaration of some arguments
                may be added

  Output: a list of expressions

 Purpose: Converts the operands of the equals function to string
          expressions and outputs these conversions. As a side effect
          of the conversions it adds some code to init_code.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::get_data_type

  Inputs:
    type - a type containing a "data" component
    symbol_table - symbol table

  Output: type of the "data" component

 Purpose: Finds the type of the data component

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::get_length_type

  Inputs:
    type - a type containing a "length" component
    symbol_table - symbol table

  Output: type of the "length" component

 Purpose: Finds the type of the length component

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::get_length

  Inputs:
    expr - an expression of structured type with length component
    symbol_table - symbol table

  Output: expression representing the "length" member

 Purpose: access length member

\*******************************************************************/

exprt java_string_library_preprocesst::get_length(
  const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(
    expr, "length", get_length_type(expr.type(), symbol_table));
}

/*******************************************************************\

Function: java_string_library_preprocesst::get_data

  Inputs:
    expr - an expression of structured type with length component
    symbol_table - symbol table

  Output: expression representing the "data" member

 Purpose: access data member

\*******************************************************************/

exprt java_string_library_preprocesst::get_data(
  const exprt &expr, const symbol_tablet &symbol_table)
{
  return member_exprt(expr, "data", get_data_type(expr.type(), symbol_table));
}

/*******************************************************************\

Function: string_refine_preprocesst::replace_char_array

  Inputs:
    array_pointer - an expression of type char array pointer
    loc - location in the source
    symbol_table - symbol table
    code - code block, in which some assignments will be added

  Output: a string expression

 Purpose: we declare a new `cprover_string` whose contents is deduced
          from the char array.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::fresh_string

  Inputs:
    type - a type for refined strings
    loc - a location in the program
    symbol_table - symbol table

  Output: a new symbol

 Purpose: add a symbol with static lifetime and name containing
          `cprover_string` and given type

\*******************************************************************/

symbol_exprt java_string_library_preprocesst::fresh_string(
  const typet &type, const source_locationt &loc, symbol_tablet &symbol_table)
{
  symbolt string_symbol=get_fresh_aux_symbol(
    type, "cprover_string", "cprover_string", loc, ID_java, symbol_table);
  string_symbol.is_static_lifetime=true;
  return string_symbol.symbol_expr();
}

/*******************************************************************\

Function: java_string_library_preprocesst::fresh_string_expr

  Inputs:
    loc - a location in the program
    symbol_table - symbol table
    code - code block to which allocation instruction will be added

  Output: a new string_expr

 Purpose: add symbols with prefix cprover_string_length and
          cprover_string_data and construct a string_expr from them.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::fresh_string_expr_symbol

  Inputs:
    loc - a location in the program
    symbol_table - symbol table
    code - code block to which allocation instruction will be added

  Output: a new expression of refined string type

 Purpose: add symbols with prefix cprover_string_length and
          cprover_string_data and construct a string_expr from them.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::allocate_fresh_string

  Inputs:
    type - a type for string
    loc - a location in the program
    symbol_table - symbol table
    code - code block to which allocation instruction will be added

  Output: a new string

 Purpose: declare a new String and allocate it

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::allocate_fresh_array

  Inputs:
    type - a type for string
    loc - a location in the program
    symbol_table - symbol table
    code - code block to which allocation instruction will be added

  Output: a new array

 Purpose: declare a new character array and allocate it

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::make_function_application

  Inputs:
    function_name - the name of the function
    arguments - a list of arguments
    type - return type of the function
    symbol_table - a symbol table

  Output: a function application representing: function_name(arguments)

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::code_assign_function_application

  Inputs:
    lhs - an expression
    function_name - the name of the function
    arguments - a list of arguments
    symbol_table - a symbol table

  Output: the following code:
          > lhs=function_name_length(arguments)

  Purpose: assign the result of a function call

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::code_return_function_application

  Inputs:
    function_name - the name of the function
    arguments - a list of arguments
    type - the return type
    symbol_table - a symbol table

  Output: the following code:
          > return function_name_length(arguments)

  Purpose: return the result of a function call

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::code_assign_function_to_string_expr

  Inputs:
    string_expr - a string expression
    function_name - the name of the function
    arguments - arguments of the function
    symbol_table - symbol table

  Output: return the following code:
          > str.length <- function_name_length(arguments)
          > str.data <- function_name_data(arguments)

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::string_expr_of_function_application

  Inputs:
    function_name - the name of the function
    arguments - arguments of the function
    loc - a location in the program
    symbol_table - symbol table
    code - code block in which we add instructions

  Output: return a string expr str and add the following code:
          > array str.data
          > str.length <- function_name_length(arguments)
          > str.data <- function_name_data(arguments)

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_components_to_java_string

  Inputs:
    lhs - expression representing the java string to assign to
    rhs_array - pointer to the array to assign
    rhs_length - length of the array to assign
    symbol_table - symbol table

  Output: return the following code:
          > lhs = { {Object}, length=rhs_length, data=rhs_array }

 Purpose: Produce code for an assignemnrt of a string expr to a
          Java string, component-wise.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_string_expr_to_java_string

  Inputs:
    lhs - an expression representing a java string
    rhs - a string expression
    symbol_table - symbol table

  Output: return the following code:
          > lhs = { {Object}, length=rhs.length, data=rhs.data }

 Purpose: Produce code for an assignemnt of a string expr to a Java
          string.

\*******************************************************************/

codet java_string_library_preprocesst::code_assign_string_expr_to_java_string(
  const exprt &lhs,
  const string_exprt &rhs,
  symbol_tablet &symbol_table)
{
  return code_assign_components_to_java_string(
    lhs, address_of_exprt(rhs.content()), rhs.length(), symbol_table);
}

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_string_expr_to_new_java_string

  Inputs:
    lhs - an expression representing a java string
    rhs - a string expression
    loc - a location in the program
    symbol_table - symbol table

  Output: return the following code:
          > data = new array[];
          > *data = rhs.data;
          > lhs = { {Object} , length=rhs.length, data=data}

 Purpose: Produce code for an assignment of a string from a string expr.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_java_string_to_string_expr

  Inputs:
    lhs - a string expression
    rhs - an expression representing a java string
    symbol_table - symbol table

  Output: return the following code:
          > lhs.length=rhs->length
          > lhs.data=*(rhs->data)

\*******************************************************************/

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
  code.add(code_assignt(lhs.content(), rhs_data));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::
            code_assign_string_literal_to_string_expr

  Inputs:
    lhs - an expression representing a java string
    tmp_string - a temporary string to hold the literal
    s - the literal to be assigned
    symbol_table - symbol table

  Output: return the following code:
          > tmp_string = "s"
          > lhs = (string_expr) tmp_string

\*******************************************************************/

codet java_string_library_preprocesst::
  code_assign_string_literal_to_string_expr(
    const string_exprt &lhs,
    const exprt &tmp_string,
    const std::string &s,
    symbol_tablet &symbol_table)
{
  code_blockt code;
  code.add(code_assignt(tmp_string, string_literal(s)));
  code.add(code_assign_java_string_to_string_expr(
    lhs, tmp_string, symbol_table));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::
    make_string_builder_append_object_code

  Inputs:
    type - type of the function called
    loc - location in the program
    symbol_table - symbol table

 Outputs: code for the StringBuilder.append(Object) function:
          > string1 = arguments[1].toString()
          > string_expr1 = string_to_string_expr(string1)
          > string_expr2 = concat(this, string_expr1)
          > this = string_expr_to_string(string_expr2)
          > return this

\*******************************************************************/

codet java_string_library_preprocesst::make_string_builder_append_object_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_typet::parameterst params=type.parameters();
  assert(params.size()==1);
  exprt this_obj=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Code to be returned
  code_blockt code;

  // String expression that will hold the result
  string_exprt string_expr1=fresh_string_expr(loc, symbol_table, code);

  exprt::operandst arguments=process_parameters(
    type.parameters(), loc, symbol_table, code);
  assert(arguments.size()==2);

  // > string1 = arguments[1].toString()
  exprt string1=fresh_string(this_obj.type(), loc, symbol_table);
  code_function_callt fun_call;
  fun_call.lhs()=string1;
  // TODO: we should look in the symbol table for such a symbol
  fun_call.function()=symbol_exprt(
    "java::java.lang.Object.toString:()Ljava/lang/String;");
  fun_call.arguments().push_back(arguments[1]);
  code_typet fun_type;
  fun_type.return_type()=string1.type();
  fun_call.function().type()=fun_type;
  code.add(fun_call);

  // > string_expr1 = string_to_string_expr(string1)
  code.add(code_assign_java_string_to_string_expr(
    string_expr1, string1, symbol_table));

  // > string_expr2 = concat(this, string1)
  exprt::operandst concat_arguments(arguments);
  concat_arguments[1]=string_expr1;
  string_exprt string_expr2=string_expr_of_function_application(
    ID_cprover_string_concat_func, concat_arguments, loc, symbol_table, code);

  // > this = string_expr
  code.add(code_assign_string_expr_to_java_string(
    this_obj, string_expr2, symbol_table));

  // > return this
  code.add(code_returnt(this_obj));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_equals_code

  Inputs:
    type - type of the function call
    loc - location in the program_invocation_name
    symbol_table - symbol table

  Outputs: Code corresponding to:
    > string_expr1 = {this->length; *this->data}
    > string_expr2 = {arg->length; *arg->data}
    > return cprover_string_equal(string_expr1, string_expr2)

  Purpose: Used to provide code for the Java String.equals(Object) function.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::
    make_string_builder_append_float_code

  Inputs:
    type - type of the function call
    loc - location in the program_invocation_name
    symbol_table - symbol table

  Outputs: Code corresponding to:
          > string1 = arguments[1].toString()
          > string_expr1 = string_to_string_expr(string1)
          > string_expr2 = concat(this, string_expr1)
          > this = string_expr_to_string(string_expr2)
          > return this

  Purpose: Used to provide code for the Java StringBuilder.append(F)
           function.

\*******************************************************************/

codet java_string_library_preprocesst::make_string_builder_append_float_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_typet::parameterst params=type.parameters();
  assert(params.size()==1);
  exprt this_obj=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Getting types
  typet length_type=string_length_type();

  // Code to be returned
  code_blockt code;

  // String expression that will hold the result
  refined_string_typet ref_type(length_type, java_char_type());
  string_exprt string_expr1=fresh_string_expr(loc, symbol_table, code);

  exprt::operandst arguments=process_parameters(
    type.parameters(), loc, symbol_table, code);
  assert(arguments.size()==2);

  // > string1 = arguments[1].toString()
  exprt string1=fresh_string(this_obj.type(), loc, symbol_table);
  code_function_callt fun_call;
  fun_call.lhs()=string1;
  // TODO: we should look in the symbol table for such a symbol
  fun_call.function()=symbol_exprt(
    "java::java.lang.Float.toString:()Ljava/lang/String;");
  fun_call.arguments().push_back(arguments[1]);
  code_typet fun_type;
  fun_type.return_type()=string1.type();
  fun_call.function().type()=fun_type;
  code.add(fun_call);

  // > string_expr1 = string_to_string_expr(string1)
  code.add(code_assign_java_string_to_string_expr(
    string_expr1, string1, symbol_table));

  // > string_expr2 = concat(this, string1)
  exprt::operandst concat_arguments(arguments);
  concat_arguments[1]=string_expr1;

  string_exprt string_expr2=string_expr_of_function_application(
    ID_cprover_string_concat_func, concat_arguments, loc, symbol_table, code);

  // > this = string_expr
  code.add(code_assign_string_expr_to_java_string(
    this_obj, string_expr2, symbol_table));

  // > return this
  code.add(code_returnt(this_obj));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::string_literal

  Inputs:
    s - a string

 Outputs: an expression representing a Java string literal with the
          given content.

 Purpose: construct a Java string literal from a constant string value

\*******************************************************************/

exprt java_string_library_preprocesst::string_literal(const std::string &s)
{
  exprt string_literal(ID_java_string_literal);
  string_literal.set(ID_value, s);
  return string_literal;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_float_to_string_code

  Inputs:
    type - type of the function call
    loc - location in the program_invocation_name
    symbol_table - symbol table

  Outputs: Code corresponding to:
          > String * str;
          > str = MALLOC(String);
          > String * tmp_string;
          > int string_expr_length;
          > char[] string_expr_content;
          > CPROVER_string string_expr_sym;
          > if arguments[1]==NaN
          > then {tmp_string="NaN"; string_expr=(string_expr)tmp_string}
          > if arguments[1]==Infinity
          > then {tmp_string="Infinity"; string_expr=(string_expr)tmp_string}
          > if 1e-3<arguments[1]<1e6
          > then string_expr=cprover_float_to_string(arguments[1])
          > else string_expr=cprover_float_to_scientific_notation_string(arg[1])
          > string_expr_sym=string_expr;
          > str=(String*) string_expr;
          > return str;

  Purpose: Provide code for the Float.toString(F) function.

\*******************************************************************/

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
  exprt tmp_string=fresh_string(type.return_type(), loc, symbol_table);

  // Declaring CPROVER_string string_expr
  string_exprt string_expr=fresh_string_expr(loc, symbol_table, code);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table, code);

  // List of the different cases
  std::vector<code_ifthenelset> case_list;

  // First case in the list is the default
  code_ifthenelset case_sci_notation;
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  // Subcase of 0.0
  // TODO: case of -0.0
  ieee_floatt zero_float(float_spec);
  zero_float.from_float(0.0);
  constant_exprt zero=zero_float.to_expr();
  case_sci_notation.cond()=ieee_float_equal_exprt(arg, zero);
  case_sci_notation.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "0.0", symbol_table);

  // Subcase of computerized scientific notation
  case_sci_notation.else_case()=code_assign_function_to_string_expr(
    string_expr, ID_cprover_string_of_float_func, {arg}, symbol_table);
  case_list.push_back(case_sci_notation);

  // Case of NaN
  code_ifthenelset case_nan;
  case_nan.cond()=isnan_exprt(arg);
  case_nan.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "NaN", symbol_table);
  case_list.push_back(case_nan);

  // Case of Infinity
  code_ifthenelset case_infinity;
  code_ifthenelset case_minus_infinity;

  case_infinity.cond()=isinf_exprt(arg);
  // Case -Infinity
  exprt isneg=extractbit_exprt(arg, float_spec.width()-1);
  case_minus_infinity.cond()=isneg;
  case_minus_infinity.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "-Infinity", symbol_table);
  case_minus_infinity.else_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "Infinity", symbol_table);
  case_infinity.then_case()=case_minus_infinity;
  case_list.push_back(case_infinity);

  // Case of simple notation
  code_ifthenelset case_simple_notation;

  ieee_floatt bound_inf_float(float_spec);
  ieee_floatt bound_sup_float(float_spec);
  bound_inf_float.from_float(1e-3);
  bound_sup_float.from_float(1e7);
  constant_exprt bound_inf=bound_inf_float.to_expr();
  constant_exprt bound_sup=bound_sup_float.to_expr();

  and_exprt is_simple_float(
    binary_relation_exprt(arg, ID_ge, bound_inf),
    binary_relation_exprt(arg, ID_lt, bound_sup));
  case_simple_notation.cond()=is_simple_float;
  case_simple_notation.then_case()=code_assign_function_to_string_expr(
    string_expr, ID_cprover_string_of_float_func, {arg}, symbol_table);
  case_list.push_back(case_simple_notation);

  // Combining all cases
  for(std::size_t i=1; i<case_list.size(); i++)
    case_list[i].else_case()=case_list[i-1];
  code.add(case_list[case_list.size()-1]);

  // str = string_expr
  code.add(code_assign_string_expr_to_java_string(
    str, string_expr, symbol_table));

  // Assign string_expr_sym = { string_expr_length, string_expr_content }
  code.add(code_assignt(string_expr_sym, string_expr));

  // Return str
  code.add(code_returnt(str));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_init_function_from_call

  Inputs:
    function_name - name of the function to be called
    type - the type of the function call
    loc - location in program
    symbol_table - the symbol table to populate
    ignore_first_arg - boolean flag telling that the first argument
                       should not be part of the arguments of the call
                       (but only used to be assigned the result)

 Outputs: code for the String.<init>(args) function:
          > cprover_string_length = fun(arg).length;
          > cprover_string_array = fun(arg).data;
          > this->length = cprover_string_length;
          > this->data = cprover_string_array;
          > cprover_string = {.=cprover_string_length, .=cprover_string_array};

  Purpose: Generate the goto code for string initialization.

\*******************************************************************/

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

/*******************************************************************\

Function: java_string_library_preprocesst::make_string_to_char_array_code

  Inputs:
    type - type of the function called
    loc - location in the source
    symbol_table - the symbol table

  Outputs: Code corresponding to
          > return_tmp0 = malloc(array[char]);
          > return_tmp0->data=&((s->data)[0])
          > return_tmp0->length=s->length

  Purpose: Used to provide our own implementation of the
           java.lang.String.toCharArray:()[C function.

\*******************************************************************/

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
  dereference_exprt deref(string_argument, string_argument.type().subtype());

  // lhs <- malloc(array[char])
  exprt lhs=fresh_array(type.return_type(), loc, symbol_table);
  allocate_dynamic_object_with_decl(
    lhs, lhs.type().subtype(), symbol_table, loc, code);

  // first_element_address is `&((string_argument->data)[0])`
  exprt data=get_data(deref, symbol_table);
  dereference_exprt deref_data(data, data.type().subtype());
  exprt first_index=from_integer(0, string_length_type());
  index_exprt first_element(deref_data, first_index, java_char_type());
  address_of_exprt first_element_address(first_element);

  // lhs->data <- &((string_argument->data)[0])
  dereference_exprt deref_lhs(lhs, lhs.type().subtype());
  exprt lhs_data=get_data(deref_lhs, symbol_table);
  code.add(code_assignt(lhs_data, first_element_address));

  // lhs->length <- s->length
  exprt rhs_length=get_length(deref, symbol_table);
  exprt lhs_length=get_length(deref_lhs, symbol_table);
  code.add(code_assignt(lhs_length, rhs_length));

  // return lhs
  code.add(code_returnt(lhs));
  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_function_from_call

  Inputs:
    function_name - name of the function to be called
    type - type of the function
    loc - location in the source
    symbol_table - symbol table

  Outputs: Code corresponding to:
           > return function_name(args);

  Purpose: Provide code for a function that calls a function from the
           solver and simply returns it.

\*******************************************************************/

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

/*******************************************************************\

Function:
    java_string_library_preprocesst::make_string_returning_function_from_call

  Inputs:
    function_name - name of the function to be called
    type - type of the function
    loc - location in the source
    symbol_table - symbol table

  Outputs: Code corresponding to:
          > string_expr = function_name(args)
          > string = new String
          > string = string_expr_to_string(string)
          > return string

  Purpose: Provide code for a function that calls a function from the
           solver and return the string_expr result as a Java string.

\*******************************************************************/

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
  // Not supported java.lang.String.<init>:(Ljava/lang/StringBuffer;)

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
  // Not supported "java.lang.String.contentEquals"
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
  // Not supported "java.lang.String.format"
  // Not supported "java.lang.String.getBytes"
  // Not supported "java.lang.String.getChars"
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
  cprover_equivalent_to_java_function
    ["java::java.lang.String.length:()I"]=
      ID_cprover_string_length_func;
  // Not supported "java.lang.String.matches"
  cprover_equivalent_to_java_function
    ["java::java.lang.String.offsetByCodePoints:(II)I"]=
      ID_cprover_string_offset_by_code_point_func;
  // Not supported "java.lang.String.regionMatches"
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.replace:(CC)Ljava/lang/String;"]=
      ID_cprover_string_replace_func;
  // Not supported "java.lang.String.replace:(LCharSequence;LCharSequence)"
  // Not supported "java.lang.String.replaceAll"
  // Not supported "java.lang.String.replaceFirst"
  // Not supported "java.lang.String.split"
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
  // Not supported "java.lang.String.toLowerCase:(Locale)"
  // Not supported "java.lang.String.toString:()"
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.toUpperCase:()Ljava/lang/String;"]=
      ID_cprover_string_to_upper_case_func;
  // Not supported "java.lang.String.toUpperCase:(Locale)"
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
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(D)Ljava/lang/String;"]=
      ID_cprover_string_of_double_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(F)Ljava/lang/String;"]=
      ID_cprover_string_of_float_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.String.valueOf:(J)Ljava/lang/String;"]=
      ID_cprover_string_of_long_func;
  // Not supported "java.lang.String.valueOf:(LObject;)"

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
    ["java::java.lang.StringBuilder.append:(Z)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:([C)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;
  // Not supported: "java.lang.StringBuilder.append:([CII)"

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/CharSequence;II)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/CharSequence;)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;

  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(D)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_double_func;
  conversion_table
    ["java::java.lang.StringBuilder.append:(F)Ljava/lang/StringBuilder;"]=
      std::bind(
        &java_string_library_preprocesst::make_string_builder_append_float_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(I)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(J)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_long_func;

  conversion_table["java::java.lang.StringBuilder.append:"
                   "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"]=
    std::bind(
      &java_string_library_preprocesst::make_string_builder_append_object_code,
      this,
      std::placeholders::_1,
      std::placeholders::_2,
      std::placeholders::_3);
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.appendCodePoint:(I)"
     "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_concat_code_point_func;
  // Not supported: "java.lang.StringBuilder.append:(Ljava/lang/StringBuffer;)"
  // Not supported: "java.lang.StringBuilder.capacity:()"
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
  // Not supported: "java.lang.StringBuilder.ensureCapacity:()"
  // Not supported: "java.lang.StringBuilder.getChars:()"
  // Not supported: "java.lang.StringBuilder.indexOf:()"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IZ)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IC)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(I[C)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(I[CII)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuilder.insert:(ILCharSequence;)"
  // Not supported "java.lang.StringBuilder.insert:(ILCharSequence;II)"
  // Not supported "java.lang.StringBuilder.insert:(ID)"
  // Not supported "java.lang.StringBuilder.insert:(IF)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(II)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(IJ)Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_long_func;
  // Not supported "java.lang.StringBuilder.insert:(ILObject;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuilder.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuilder;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuilder.lastIndexOf"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuilder.length:()I"]=
      ID_cprover_string_length_func;
  // Not supported "java.lang.StringBuilder.offsetByCodePoints"
  // Not supported "java.lang.StringBuilder.replace"
  // Not supported "java.lang.StringBuilder.reverse"
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuilder.setCharAt:(IC)V"]=
      ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuilder.setLength:(I)V"]=
      ID_cprover_string_set_length_func;
  // Not supported "java.lang.StringBuilder.subSequence"
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
  // Not supported "java.lang.StringBuilder.trimToSize"
  // TODO clean irep ids from insert_char_array etc...

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
    ["java::java.lang.StringBuffer.append:(Z)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:([C)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  // Not supported: "java.lang.StringBuffer.append:([CII)"
  // Not supported: "java.lang.StringBuffer.append:(LCharSequence;)"
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
  // Not supported: "java.lang.StringBuffer.append:(LObject;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.appendCodePoint:(I)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_concat_code_point_func;
  // Not supported: "java.lang.StringBuffer.append:(Ljava/lang/StringBuffer;)"
  // Not supported: "java.lang.StringBuffer.capacity:()"
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
  // Not supported: "java.lang.StringBuffer.ensureCapacity:()"
  // Not supported: "java.lang.StringBuffer.getChars:()"
  // Not supported: "java.lang.StringBuffer.indexOf:()"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IZ)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_bool_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IC)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_char_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(I[C)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(I[CII)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuffer.insert:(ILCharSequence;)"
  // Not supported "java.lang.StringBuffer.insert:(ILCharSequence;II)"
  // Not supported "java.lang.StringBuffer.insert:(ID)"
  // Not supported "java.lang.StringBuffer.insert:(IF)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(II)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_int_func;
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(IJ)Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_long_func;
  // Not supported "java.lang.StringBuffer.insert:(ILObject;)"
  cprover_equivalent_to_java_assign_and_return_function
    ["java::java.lang.StringBuffer.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuffer;"]=
      ID_cprover_string_insert_func;
  // Not supported "java.lang.StringBuffer.lastIndexOf"
  cprover_equivalent_to_java_function
    ["java::java.lang.StringBuffer.length:()I"]=
      ID_cprover_string_length_func;
  // Not supported "java.lang.StringBuffer.offsetByCodePoints"
  // Not supported "java.lang.StringBuffer.replace"
  // Not supported "java.lang.StringBuffer.reverse"
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuffer.setCharAt:(IC)V"]=
      ID_cprover_string_char_set_func;
  cprover_equivalent_to_java_assign_function
    ["java::java.lang.StringBuffer.setLength:(I)V"]=
    ID_cprover_string_set_length_func;
  // Not supported "java.lang.StringBuffer.subSequence"
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuffer.substring:(II)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.StringBuffer.substring:(I)Ljava/lang/String;"]=
      ID_cprover_string_substring_func;
  conversion_table
    ["java::java.lang.StringBuffer.toString:()Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_copy_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  // Not supported "java.lang.StringBuffer.trimToSize"

  // Other libraries
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
    ["java::java.lang.Float.toString:(F)Ljava/lang/String;"]=
      std::bind(
        &java_string_library_preprocesst::make_float_to_string_code,
        this,
        std::placeholders::_1,
        std::placeholders::_2,
        std::placeholders::_3);
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.Integer.toHexString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_hex_func;
  cprover_equivalent_to_java_function
    ["java::java.lang.Integer.parseInt:(Ljava/lang/String;)I"]=
      ID_cprover_string_parse_int_func;
  cprover_equivalent_to_java_string_returning_function
    ["java::java.lang.Integer.toString:(I)Ljava/lang/String;"]=
      ID_cprover_string_of_int_func;
}
