/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the string solver

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/string_expr.h>
#include <util/refined_string_type.h>
#include <util/fresh_symbol.h>
#include <goto-programs/class_identifier.h>
#include <java_bytecode/java_types.h>

#include "string_refine_preprocess.h"

/*******************************************************************\

Function: string_refine_preprocesst::check_java_type

  Inputs: a type and a string

 Outputs: Boolean telling whether the type is a struct with the given
          tag or a symbolic type with the tag prefixed by "java::"

\*******************************************************************/

bool string_refine_preprocesst::check_java_type(
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

Function: string_refine_preprocesst::is_java_string_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string pointers

\*******************************************************************/

bool string_refine_preprocesst::is_java_string_pointer_type(const typet &type)
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

Function: string_refine_preprocesst::is_java_string_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string

\*******************************************************************/

bool string_refine_preprocesst::is_java_string_type(const typet &type)
{
  return check_java_type(type, "java.lang.String");
}

/*******************************************************************\

Function: string_refine_preprocesst::is_java_string_builder_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string builder

\*******************************************************************/

bool string_refine_preprocesst::is_java_string_builder_type(const typet &type)
{
  return check_java_type(type, "java.lang.StringBuilder");
}

/*******************************************************************\

Function: string_refine_preprocesst::is_java_string_builder_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuilder
          pointers

\*******************************************************************/

bool string_refine_preprocesst::is_java_string_builder_pointer_type(
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

Function: string_refine_preprocesst::is_java_char_sequence_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char sequence

\*******************************************************************/

bool string_refine_preprocesst::is_java_char_sequence_type(const typet &type)
{
  return check_java_type(type, "java.lang.CharSequence");
}

/*******************************************************************\

Function: string_refine_preprocesst::is_java_char_sequence_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char sequence

\*******************************************************************/

bool string_refine_preprocesst::is_java_char_sequence_pointer_type(
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

Function: string_refine_preprocesst::is_java_char_array_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char array

\*******************************************************************/

bool string_refine_preprocesst::is_java_char_array_type(const typet &type)
{
  return check_java_type(type, "array[char]");
}

/*******************************************************************\

Function: string_refine_preprocesst::is_java_char_array_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char array

\*******************************************************************/

bool string_refine_preprocesst::is_java_char_array_pointer_type(
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

Function: string_refine_preprocesst::fresh_array

  Inputs:
    type - an array type
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol with static lifetime and name containing
          `cprover_string_array` and given type

\*******************************************************************/

symbol_exprt string_refine_preprocesst::fresh_array(
  const typet &type, const source_locationt &location)
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

/*******************************************************************\

Function: string_refine_preprocesst::fresh_string

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol with static lifetime and name containing
          `cprover_string` and given type

\*******************************************************************/

symbol_exprt string_refine_preprocesst::fresh_string(
  const typet &type, const source_locationt &location)
{
  symbolt array_symbol=get_fresh_aux_symbol(
    type, "cprover_string", "cprover_string", location, ID_java, symbol_table);
  array_symbol.is_static_lifetime=true;
  return array_symbol.symbol_expr();
}

/*******************************************************************\

Function: string_refine_preprocesst::declare_function

  Inputs: a name and a type

 Purpose: declare a function with the given name and type

\*******************************************************************/

void string_refine_preprocesst::declare_function(
  irep_idt function_name, const typet &type)
{
  auxiliary_symbolt func_symbol;
  func_symbol.base_name=function_name;
  func_symbol.is_static_lifetime=false;
  func_symbol.mode=ID_java;
  func_symbol.name=function_name;
  func_symbol.type=type;
  symbol_table.add(func_symbol);
  goto_functions.function_map[function_name];
}

/*******************************************************************\

Function: string_refine_preprocesst::get_data_and_length_type_of_char_array

  Inputs: an expression, a reference to a data type and a reference to a
          length type

 Purpose: assuming the expression is a char array, figure out what
          the types for length and data are and put them into the references
          given as argument

\*******************************************************************/

void string_refine_preprocesst::get_data_and_length_type_of_char_array(
  const exprt &expr, typet &data_type, typet &length_type)
{
  typet object_type=ns.follow(expr.type());
  assert(object_type.id()==ID_struct);
  const struct_typet &struct_type=to_struct_type(object_type);
  for(auto component : struct_type.components())
    if(component.get_name()=="length")
      length_type=component.type();
    else if(component.get_name()=="data")
      data_type=component.type();
}

/*******************************************************************\

Function: string_refine_preprocesst::get_data_and_length_type_of_string

  Inputs: an expression, a reference to a data type and a reference to a
          length type

 Purpose: assuming the expression is a java string, figure out what
          the types for length and data are and put them into the references
          given as argument

\*******************************************************************/

void string_refine_preprocesst::get_data_and_length_type_of_string(
  const exprt &expr, typet &data_type, typet &length_type)
{
  assert(is_java_string_type(expr.type()) ||
         is_java_string_builder_type(expr.type()) ||
         is_java_char_sequence_type(expr.type()));
  typet object_type=ns.follow(expr.type());
  const struct_typet &struct_type=to_struct_type(object_type);
  for(const auto &component : struct_type.components())
    if(component.get_name()=="length")
      length_type=component.type();
    else if(component.get_name()=="data")
      data_type=component.type();
}

/*******************************************************************\

Function: string_refine_preprocesst::make_cprover_string_assign

  Inputs: a goto_program, a position in this program, an expression and a
          location

 Outputs: an expression

 Purpose: Introduce a temporary variable for cprover strings;
          returns the cprover_string corresponding to rhs if it is a string
          pointer and the original rhs otherwise.

\*******************************************************************/

exprt string_refine_preprocesst::make_cprover_string_assign(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const exprt &rhs,
  const source_locationt &location)
{
  if(implements_java_char_sequence(rhs.type()))
  {
    // We do the following assignments:
    // 1 length= *(rhs->length)
    // 2 cprover_string_array = *(rhs->data)
    // 3 cprover_string = { length; cprover_string_array }

    dereference_exprt deref(rhs, rhs.type().subtype());
    typet data_type, length_type;
    get_data_and_length_type_of_string(deref, data_type, length_type);
    std::list<code_assignt> assignments;

    // 1) cprover_string_length= *(rhs->length)
    symbolt sym_length=get_fresh_aux_symbol(
      length_type,
      "cprover_string_length",
      "cprover_string_length",
      location,
      ID_java,
      symbol_table);
    symbol_exprt cprover_length=sym_length.symbol_expr();
    member_exprt length(deref, "length", length_type);
    assignments.emplace_back(cprover_length, length);

    // 2) cprover_string_array = *(rhs->data)
    symbol_exprt array_lhs=fresh_array(data_type.subtype(), location);
    member_exprt data(deref, "data", data_type);
    dereference_exprt deref_data(data, data_type.subtype());
    assignments.emplace_back(array_lhs, deref_data);

    // 3) cprover_string = { cprover_string_length; cprover_string_array }
    // This assignment is useful for finding witnessing strings for counter
    // examples
    refined_string_typet ref_type(length_type, java_char_type());
    string_exprt new_rhs(cprover_length, array_lhs, ref_type);

    symbol_exprt lhs=fresh_string(new_rhs.type(), location);
    assignments.emplace_back(lhs, new_rhs);

    insert_assignments(
      goto_program, target, target->function, location, assignments);
    target=goto_program.insert_after(target);
    return new_rhs;
  }
  else if(rhs.id()==ID_typecast &&
          implements_java_char_sequence(rhs.op0().type()))
  {
    exprt new_rhs=make_cprover_string_assign(
      goto_program, target, rhs.op0(), location);
    return typecast_exprt(new_rhs, rhs.type());
  }
  else
    return rhs;
}

/*******************************************************************\

Function: string_refine_preprocesst::make_cprover_char_array_assign

  Inputs: a goto_program, a position in this program, an expression of
          type char array pointer and a location

 Outputs: a string expression

 Purpose: Introduce a temporary variable for cprover strings;
          returns the cprover_string corresponding to rhs

\*******************************************************************/

string_exprt string_refine_preprocesst::make_cprover_char_array_assign(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const exprt &rhs,
  const source_locationt &location)
{
  assert(is_java_char_array_pointer_type(rhs.type()));

  // We do the following assignments:
  // deref=*(rhs->data)
  // array= typecast(&deref);
  // string={ rhs->length; array }

  dereference_exprt deref(rhs, rhs.type().subtype());
  typet length_type, data_type;
  get_data_and_length_type_of_char_array(deref, data_type, length_type);
  assert(data_type.id()==ID_pointer);
  typet char_type=to_pointer_type(data_type).subtype();

  refined_string_typet ref_type(length_type, java_char_type());
  typet content_type=ref_type.get_content_type();
  std::list<code_assignt> assignments;

  // deref=*(rhs->data)
  member_exprt array_rhs(deref, "data", data_type);
  dereference_exprt deref_array(array_rhs, data_type.subtype());
  symbolt sym_lhs_deref=get_fresh_aux_symbol(
    data_type.subtype(),
    "char_array_assign$deref",
    "char_array_assign$deref",
    location,
    ID_java,
    symbol_table);
  symbol_exprt lhs_deref=sym_lhs_deref.symbol_expr();
  assignments.emplace_back(lhs_deref, deref_array);

  // array=convert_pointer_to_char_array(*rhs->data)
  declare_function(ID_cprover_string_array_of_char_pointer_func, content_type);
  function_application_exprt fun_app(symbol_exprt(
    ID_cprover_string_array_of_char_pointer_func), content_type);
  fun_app.arguments().push_back(deref_array);
  symbol_exprt array=fresh_array(content_type, location);
  assignments.emplace_back(array, fun_app);

  // string={ rhs->length; string_array }
  string_exprt new_rhs(get_length(deref, length_type), array, ref_type);
  symbol_exprt lhs=fresh_string(ref_type, location);
  assignments.emplace_back(lhs, new_rhs);

  insert_assignments(
    goto_program, target, target->function, location, assignments);
  target=goto_program.insert_after(target);
  return new_rhs;
}

/*******************************************************************\

Function: string_refine_preprocesst::make_normal_assign

  Inputs: a goto_program, a position in this program, an expression lhs,
          a function type, a function name, a vector of arguments, a location
          and a signature

 Purpose: replace the current instruction by:
          > lhs=function_name(arguments) : return_type @ location
          If given, signature can force String conversion of given arguments.
          The convention for signature is one character by argument
          and 'S' denotes string.

\*******************************************************************/

void string_refine_preprocesst::make_normal_assign(
  goto_programt &goto_program,
  goto_programt::targett target,
  const exprt &lhs,
  const code_typet &function_type,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const source_locationt &location,
  const std::string &signature)
{
  function_application_exprt rhs(
    symbol_exprt(function_name), function_type.return_type());
  rhs.add_source_location()=location;
  declare_function(function_name, function_type);

  exprt::operandst processed_arguments=process_arguments(
    goto_program, target, arguments, location, signature);
  rhs.arguments()=processed_arguments;

  code_assignt assignment(lhs, rhs);
  assignment.add_source_location()=location;
  target->make_assignment();
  target->code=assignment;
}

/*******************************************************************\

Function: string_refine_preprocesst::insert_assignments

  Inputs: a goto_program, a position in this program, a list of assignments

 Purpose: add the assignments to the program in the order they are given

\*******************************************************************/

void string_refine_preprocesst::insert_assignments(
  goto_programt &goto_program,
  goto_programt::targett &target,
  irep_idt function,
  source_locationt location,
  const std::list<code_assignt> &va)
{
  if(va.empty())
    return;

  auto i=va.begin();
  target->make_assignment();
  target->code=*i;
  target->function=function;
  target->source_location=location;
  for(i++; i!=va.end(); i++)
  {
    target=goto_program.insert_after(target);
    target->make_assignment();
    target->code=*i;
    target->function=function;
    target->source_location=location;
  }
}

/*******************************************************************\

Function: string_refine_preprocesst::make_string_assign

  Inputs: a goto_program, a position in this program, an expression lhs,
          a function type, a function name, a vector of arguments, a location
          and a signature

 Purpose: replace the current instruction by:
          > lhs=malloc(String *)
          > lhs->length=function_name_length(arguments)
          > tmp_data=function_name_data(arguments)
          > lhs->data=&tmp_data

\*******************************************************************/

void string_refine_preprocesst::make_string_assign(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const exprt &lhs,
  const code_typet &function_type,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const source_locationt &location,
  const std::string &signature)
{
  assert(implements_java_char_sequence(function_type.return_type()));
  dereference_exprt deref(lhs, lhs.type().subtype());
  typet object_type=ns.follow(deref.type());
  exprt object_size=size_of_expr(object_type, ns);
  typet length_type, data_type;
  get_data_and_length_type_of_string(deref, data_type, length_type);

  std::string fnamel=id2string(function_name)+"_length";
  std::string fnamed=id2string(function_name)+"_data";
  declare_function(fnamel, length_type);
  declare_function(fnamed, data_type);
  function_application_exprt rhs_length(symbol_exprt(fnamel), length_type);
  function_application_exprt rhs_data(
    symbol_exprt(fnamed), data_type.subtype());

  exprt::operandst processed_arguments=process_arguments(
    goto_program, target, arguments, location, signature);
  rhs_length.arguments()=processed_arguments;
  rhs_data.arguments()=processed_arguments;

  symbolt sym_length=get_fresh_aux_symbol(
    length_type, "length", "length", location, ID_java, symbol_table);
  symbol_exprt tmp_length=sym_length.symbol_expr();
  symbol_exprt tmp_array=fresh_array(data_type.subtype(), location);
  member_exprt lhs_length(deref, "length", length_type);
  member_exprt lhs_data(deref, "data", tmp_array.type());

  // lhs=malloc(String *)
  assert(object_size.is_not_nil()); // got nil object_size
  side_effect_exprt malloc_expr(ID_malloc);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.type()=pointer_typet(object_type);
  malloc_expr.add_source_location()=location;

  refined_string_typet ref_type(length_type, data_type.subtype().subtype());
  string_exprt str(tmp_length, tmp_array, ref_type);
  symbol_exprt cprover_string_sym=fresh_string(ref_type, location);

  std::list<code_assignt> assigns;
  assigns.emplace_back(lhs, malloc_expr);
  assigns.emplace_back(tmp_length, rhs_length);
  assigns.emplace_back(lhs_length, tmp_length);
  assigns.emplace_back(tmp_array, rhs_data);
  assigns.emplace_back(cprover_string_sym, str);
  assigns.emplace_back(lhs_data, address_of_exprt(tmp_array));
  insert_assignments(goto_program, target, target->function, location, assigns);
}

/*******************************************************************\

Function: string_refine_preprocesst::make_string_function

  Inputs: a position in a goto program, a function name, an expression lhs,
          a function type, name, arguments, a location and a signature string

 Purpose: at the current position replace `lhs=s.some_function(x,...)`
          by `lhs=function_name(s,x,...)`;

\*******************************************************************/

void string_refine_preprocesst::make_string_function(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const exprt &lhs,
  const code_typet &function_type,
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const source_locationt &location,
  const std::string &signature)
{
  if(signature.length()>0)
  {
    if(signature.back()=='S')
    {
      code_typet ft=function_type;
      ft.return_type()=jls_ptr;
      typecast_exprt lhs2(lhs, jls_ptr);

      make_string_assign(
        goto_program,
        target,
        lhs2,
        ft,
        function_name,
        arguments,
        location,
         signature);
    }
    else
      make_normal_assign(
      goto_program,
      target,
      lhs,
      function_type,
      function_name,
      arguments,
      location,
      signature);
  }
  else if(implements_java_char_sequence(function_type.return_type()))
    make_string_assign(
      goto_program,
      target,
      lhs,
      function_type,
      function_name,
      arguments,
      location,
      signature);
  else
    make_normal_assign(
      goto_program,
      target,
      lhs,
      function_type,
      function_name,
      arguments,
      location,
      signature);
}

/*******************************************************************\

Function: string_refine_preprocesst::make_string_function

  Inputs: a position in a goto program, a function name and two Boolean options

 Purpose: at the current position replace `lhs=s.some_function(x,...)`
          by `lhs=function_name(s,x,...)`;
          option `assign_first_arg` uses `s` instead of `lhs` in the resulting
          expression, Warning : it assumes that `s` is string-like
          option `skip_first_arg`, removes `s` from the arguments, ie `x` is
          the first one;
          arguments that are string (TODO: and char array) are replaced
          by string_exprt

\*******************************************************************/

void string_refine_preprocesst::make_string_function(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const irep_idt &function_name,
  const std::string &signature,
  bool assign_first_arg,
  bool skip_first_arg)
{
  code_function_callt &function_call=to_code_function_call(target->code);
  code_typet function_type=to_code_type(function_call.function().type());
  code_typet new_type;
  const source_locationt &loc=function_call.source_location();
  declare_function(function_name, function_type);
  function_application_exprt rhs;
  std::vector<exprt> args;
  if(assign_first_arg)
  {
    assert(!function_call.arguments().empty());
    rhs.type()=function_call.arguments()[0].type();
  }
  else
    rhs.type()=function_type.return_type();
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);

  std::size_t start_index=skip_first_arg?1:0;
  for(std::size_t i=start_index; i<function_call.arguments().size(); i++)
  {
    args.push_back(function_call.arguments()[i]);
    new_type.parameters().push_back(function_type.parameters()[i]);
  }

  std::string new_sig=signature;
  exprt lhs;
  if(assign_first_arg)
  {
    assert(!function_call.arguments().empty());
    lhs=function_call.arguments()[0];
    std::size_t size=function_call.arguments().size();
    if(signature.length()<=size)
      new_sig.resize(size+1, '_');

    new_sig.replace(size, 1, "S");
  }
  else
    lhs=function_call.lhs();

  if(lhs.id()==ID_typecast)
    lhs=to_typecast_expr(lhs).op();

  new_type.return_type()=lhs.type();

  make_string_function(
    goto_program, target, lhs, new_type, function_name, args, loc, new_sig);
}

/*******************************************************************\

Function: string_refine_preprocesst::make_string_function_call

  Inputs: a position in a goto program and a function name

 Purpose: at the current position, replace `s.some_function(x,...)` by
          `s=function_name(x,...)`

\*******************************************************************/

void string_refine_preprocesst::make_string_function_call(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const irep_idt &function_name,
  const std::string &signature)
{
  make_string_function(
    goto_program, target, function_name, signature, true, true);
}

/*******************************************************************\

Function: string_refine_preprocesst::make_string_function_side_effect

  Inputs: a position in a goto program and a function name

 Purpose: at the current position, replace `r=s.some_function(x,...)` by
          > tmp=function_name(x,...)
          > s->data=tmp.data
          > s->length=tmp.length
          > r=s

\*******************************************************************/

void string_refine_preprocesst::make_string_function_side_effect(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const irep_idt &function_name,
  const std::string &signature)
{
  code_function_callt function_call=to_code_function_call(target->code);
  source_locationt loc=function_call.source_location();
  std::list<code_assignt> assignments;
  exprt lhs=function_call.lhs();
  exprt s=function_call.arguments()[0];
  code_typet function_type=to_code_type(function_call.type());

  function_type.return_type()=s.type();

  if(lhs.is_not_nil())
  {
    symbol_exprt tmp_string=fresh_string(lhs.type(), loc);

    make_string_assign(
      goto_program,
      target,
      tmp_string,
      function_type,
      function_name,
      function_call.arguments(),
      loc,
      signature);
    dereference_exprt deref_lhs(s, s.type().subtype());
    typet data_type, length_type;
    get_data_and_length_type_of_string(deref_lhs, data_type, length_type);
    member_exprt lhs_data(deref_lhs, "data", data_type);
    member_exprt lhs_length(deref_lhs, "length", length_type);
    dereference_exprt deref_rhs(tmp_string, s.type().subtype());
    member_exprt rhs_data(deref_rhs, "data", data_type);
    member_exprt rhs_length(deref_rhs, "length", length_type);
    assignments.emplace_back(lhs_length, rhs_length);
    assignments.emplace_back(lhs_data, rhs_data);
    assignments.emplace_back(lhs, s);
    target=goto_program.insert_after(target);
    insert_assignments(
      goto_program, target, target->function, loc, assignments);
  }
  else
  {
    make_string_function(
      goto_program, target, function_name, signature, true, false);
  }
}

/*******************************************************************\

Function: string_refine_preprocesst::build_function_application

  Inputs: a function name, a type, a location and a vector of arguments

 Outputs: a function application expression

 Purpose: declare a function and construct an function application expression
          with the given function name, type, location and arguments

\*******************************************************************/

function_application_exprt
  string_refine_preprocesst::build_function_application(
    const irep_idt &function_name,
    const typet &type,
    const source_locationt &location,
    const exprt::operandst &arguments)
{
  declare_function(function_name, type);
  function_application_exprt function_app(symbol_exprt(function_name), type);
  function_app.add_source_location()=location;
  for(const auto &arg : arguments)
    function_app.arguments().push_back(arg);

  return function_app;
}

/*******************************************************************\

Function: string_refine_preprocesst::make_to_char_array_function

  Inputs: a goto program and a position in that goto program

 Purpose: at the given position replace `return_tmp0=s.toCharArray()` with:
          > return_tmp0 = malloc(array[char]);
          > return_tmp0->data=&((s->data)[0])
          > return_tmp0->length=s->length

\*******************************************************************/

void string_refine_preprocesst::make_to_char_array_function(
  goto_programt &goto_program, goto_programt::targett &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();

  assert(function_call.arguments().size()>=1);
  const exprt &string_argument=function_call.arguments()[0];
  assert(is_java_string_pointer_type(string_argument.type()));

  typet deref_type=function_call.lhs().type().subtype();
  const exprt &lhs=function_call.lhs();
  dereference_exprt deref_lhs(lhs, deref_type);

  dereference_exprt deref(string_argument, string_argument.type().subtype());
  typet length_type, data_type;
  get_data_and_length_type_of_string(deref, data_type, length_type);
  std::list<code_assignt> assignments;

  // lhs=malloc(array[char])
  typet object_type=ns.follow(deref_type);
  exprt object_size=size_of_expr(object_type, ns);

  if(object_size.is_nil())
    debug() << "string_refine_preprocesst::make_to_char_array_function "
            << "got nil object_size" << eom;

  side_effect_exprt malloc_expr(ID_malloc);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.type()=pointer_typet(object_type);
  malloc_expr.add_source_location()=location;
  assignments.emplace_back(lhs, malloc_expr);


  // &((s->data)[0])
  exprt rhs_data=get_data(deref, data_type);
  dereference_exprt rhs_array(rhs_data, data_type.subtype());
  exprt first_index=from_integer(0, java_int_type());
  index_exprt first_element(rhs_array, first_index, java_char_type());
  address_of_exprt rhs_pointer(first_element);

  // return_tmp0->data=&((s->data)[0])
  exprt lhs_data=get_data(deref_lhs, data_type);
  assignments.emplace_back(lhs_data, rhs_pointer);

  // return_tmp0->length=s->length
  exprt rhs_length=get_length(deref, length_type);
  exprt lhs_length=get_length(deref_lhs, length_type);
  assignments.emplace_back(lhs_length, rhs_length);
  insert_assignments(
    goto_program, target, target->function, location, assignments);
}

/*******************************************************************\

Function: string_refine_preprocesst::process_arguments

  Inputs: a goto program, a position, a list of expressions, a location and a
          signature

 Outputs: a list of expressions

 Purpose: for each expression that is a string or that is at a position with
          an 'S' character in the signature, we declare a new `cprover_string`
          whose contents is deduced from the expression and replace the
          expression by this cprover_string in the output list;
          in the other case the expression is kept as is for the output list.

\*******************************************************************/

exprt::operandst string_refine_preprocesst::process_arguments(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const exprt::operandst &arguments,
  const source_locationt &location,
  const std::string &signature)
{
  exprt::operandst new_arguments;

  for(std::size_t i=0; i<arguments.size(); i++)
  {
    exprt arg=arguments[i];
    if(i<signature.length() && signature[i]=='S')
    {
      while(arg.id()==ID_typecast)
        arg=arg.op0();
      if(!implements_java_char_sequence(arg.type()))
        arg=typecast_exprt(arg, jls_ptr);
    }
    arg=make_cprover_string_assign(goto_program, target, arg, location);
    typet type=ns.follow(arg.type());
    if(is_java_char_array_pointer_type(type))
    {
      arg=make_cprover_char_array_assign(goto_program, target, arg, location);
    }
    new_arguments.push_back(arg);
  }
  return new_arguments;
}

/*******************************************************************\

Function: string_refine_preprocesst::function_signature

  Inputs: the name of a cprover string function

 Outputs: a signature string

 Purpose: if the signature of the given function is defined, return it
          otherwise return an empty string

\*******************************************************************/

std::string string_refine_preprocesst::function_signature(
  const irep_idt &function_id)
{
  auto it=signatures.find(function_id);
  if(it!=signatures.end())
    return it->second;
  else
    return "";
}

/*******************************************************************\

Function: string_refine_preprocesst::replace_string_calls

  Inputs: a function in a goto_program

 Purpose: goes through the instructions, replace function calls to string
          function by equivalent instructions using functions defined
          for the string solver, replace string literals by string
          expressions of the type used by the string solver
          TODO: the current implementation is only for java functions,
          we should add support for other languages

\*******************************************************************/

void string_refine_preprocesst::replace_string_calls(
  goto_functionst::function_mapt::iterator f_it)
{
  goto_programt &goto_program=f_it->second.body;

  Forall_goto_program_instructions(target, goto_program)
  {
    if(target->is_function_call())
    {
      code_function_callt &function_call=to_code_function_call(target->code);

      if(function_call.function().id()==ID_symbol)
      {
        const irep_idt &function_id=
          to_symbol_expr(function_call.function()).get_identifier();
        std::string signature=function_signature(function_id);

        auto it=string_functions.find(function_id);
        if(it!=string_functions.end())
          make_string_function(
            goto_program, target, it->second, signature, false, false);

        it=side_effect_functions.find(function_id);
        if(it!=side_effect_functions.end())
          make_string_function_side_effect(
            goto_program, target, it->second, signature);

        it=string_function_calls.find(function_id);
        if(it!=string_function_calls.end())
          make_string_function_call(
            goto_program, target, it->second, signature);

        if(function_id==irep_idt("java::java.lang.String.toCharArray:()[C"))
          make_to_char_array_function(goto_program, target);
      }
    }
    else
    {
      if(target->is_assign())
      {
        // In assignments we replace string literals and C string functions
        code_assignt assignment=to_code_assign(target->code);

        exprt new_rhs=assignment.rhs();
        code_assignt new_assignment(assignment.lhs(), new_rhs);

        if(new_rhs.id()==ID_function_application)
        {
          function_application_exprt f=to_function_application_expr(new_rhs);
          const exprt &name=f.function();
          assert(name.id()==ID_symbol);
          const irep_idt &id=to_symbol_expr(name).get_identifier();
          auto it=c_string_functions.find(id);
          if(it!=c_string_functions.end())
          {
            declare_function(it->second, f.type());
            f.function()=symbol_exprt(it->second);
            new_assignment=code_assignt(assignment.lhs(), f);
          }
        }

        new_assignment.add_source_location()=assignment.source_location();
        target->make_assignment();
        target->code=new_assignment;
      }
    }
  }
  return;
}

/*******************************************************************\

Function: string_refine_preprocesst::initialize_string_function_table

 Purpose: fill maps with correspondance from java method names to cprover
          functions

\*******************************************************************/

void string_refine_preprocesst::initialize_string_function_table()
{
  string_functions["java::java.lang.String.codePointAt:(I)I"]=
    ID_cprover_string_code_point_at_func;
  string_functions["java::java.lang.String.codePointBefore:(I)I"]=
    ID_cprover_string_code_point_before_func;
  string_functions["java::java.lang.String.codePointCount:(II)I"]=
    ID_cprover_string_code_point_count_func;
  string_functions["java::java.lang.String.offsetByCodePoints:(II)I"]=
    ID_cprover_string_offset_by_code_point_func;
  string_functions["java::java.lang.String.hashCode:()I"]=
    ID_cprover_string_hash_code_func;
  string_functions["java::java.lang.String.indexOf:(I)I"]=
    ID_cprover_string_index_of_func;
  string_functions["java::java.lang.String.indexOf:(II)I"]=
    ID_cprover_string_index_of_func;
  string_functions["java::java.lang.String.indexOf:(Ljava/lang/String;)I"]=
    ID_cprover_string_index_of_func;
  string_functions["java::java.lang.String.indexOf:(Ljava/lang/String;I)I"]=
    ID_cprover_string_index_of_func;
  string_functions["java::java.lang.String.lastIndexOf:(I)I"]=
    ID_cprover_string_last_index_of_func;
  string_functions["java::java.lang.String.lastIndexOf:(II)I"]=
    ID_cprover_string_last_index_of_func;
  string_functions
    ["java::java.lang.String.lastIndexOf:(Ljava/lang/String;)I"]=
    ID_cprover_string_last_index_of_func;
  string_functions
    ["java::java.lang.String.lastIndexOf:(Ljava/lang/String;I)I"]=
    ID_cprover_string_last_index_of_func;
  string_functions
    ["java::java.lang.String.concat:(Ljava/lang/String;)Ljava/lang/String;"]=
    ID_cprover_string_concat_func;
  string_functions["java::java.lang.String.length:()I"]=
    ID_cprover_string_length_func;
  string_functions["java::java.lang.StringBuilder.length:()I"]=
    ID_cprover_string_length_func;
  string_functions["java::java.lang.String.equals:(Ljava/lang/Object;)Z"]=
    ID_cprover_string_equal_func;
  string_functions
    ["java::java.lang.String.equalsIgnoreCase:(Ljava/lang/String;)Z"]=
    ID_cprover_string_equals_ignore_case_func;
  string_functions["java::java.lang.String.startsWith:(Ljava/lang/String;)Z"]=
    ID_cprover_string_startswith_func;
  string_functions
    ["java::java.lang.String.startsWith:(Ljava/lang/String;I)Z"]=
    ID_cprover_string_startswith_func;
  string_functions["java::java.lang.String.endsWith:(Ljava/lang/String;)Z"]=
    ID_cprover_string_endswith_func;
  string_functions["java::java.lang.String.substring:(II)Ljava/lang/String;"]=
    ID_cprover_string_substring_func;
  string_functions["java::java.lang.String.substring:(II)Ljava/lang/String;"]=
    ID_cprover_string_substring_func;
  string_functions["java::java.lang.String.substring:(I)Ljava/lang/String;"]=
    ID_cprover_string_substring_func;
  string_functions
    ["java::java.lang.StringBuilder.substring:(II)Ljava/lang/String;"]=
    ID_cprover_string_substring_func;
  string_functions
    ["java::java.lang.StringBuilder.substring:(I)Ljava/lang/String;"]=
    ID_cprover_string_substring_func;
  string_functions
    ["java::java.lang.String.subSequence:(II)Ljava/lang/CharSequence;"]=
    ID_cprover_string_substring_func;
  string_functions["java::java.lang.String.trim:()Ljava/lang/String;"]=
    ID_cprover_string_trim_func;
  string_functions["java::java.lang.String.toLowerCase:()Ljava/lang/String;"]=
    ID_cprover_string_to_lower_case_func;
  string_functions["java::java.lang.String.toUpperCase:()Ljava/lang/String;"]=
    ID_cprover_string_to_upper_case_func;
  string_functions["java::java.lang.String.replace:(CC)Ljava/lang/String;"]=
    ID_cprover_string_replace_func;
  string_functions
    ["java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z"]=
    ID_cprover_string_contains_func;
  string_functions["java::java.lang.String.compareTo:(Ljava/lang/String;)I"]=
    ID_cprover_string_compare_to_func;
  string_functions["java::java.lang.String.intern:()Ljava/lang/String;"]=
    ID_cprover_string_intern_func;
  string_functions["java::java.lang.String.isEmpty:()Z"]=
    ID_cprover_string_is_empty_func;
  string_functions["java::java.lang.String.charAt:(I)C"]=
    ID_cprover_string_char_at_func;
  string_functions["java::java.lang.StringBuilder.charAt:(I)C"]=
    ID_cprover_string_char_at_func;
  string_functions["java::java.lang.CharSequence.charAt:(I)C"]=
    ID_cprover_string_char_at_func;
  string_functions
    ["java::java.lang.StringBuilder.toString:()Ljava/lang/String;"]=
    ID_cprover_string_copy_func;

  string_functions["java::java.lang.String.valueOf:(F)Ljava/lang/String;"]=
    ID_cprover_string_of_float_func;
  string_functions["java::java.lang.Float.toString:(F)Ljava/lang/String;"]=
    ID_cprover_string_of_float_func;
  string_functions["java::java.lang.Integer.toString:(I)Ljava/lang/String;"]=
    ID_cprover_string_of_int_func;
  string_functions["java::java.lang.String.valueOf:(I)Ljava/lang/String;"]=
    ID_cprover_string_of_int_func;
  string_functions["java::java.lang.Integer.toHexString:(I)Ljava/lang/String;"]=
    ID_cprover_string_of_int_hex_func;
  string_functions["java::java.lang.String.valueOf:(L)Ljava/lang/String;"]=
    ID_cprover_string_of_long_func;
  string_functions["java::java.lang.String.valueOf:(D)Ljava/lang/String;"]=
    ID_cprover_string_of_double_func;
  string_functions["java::java.lang.String.valueOf:(Z)Ljava/lang/String;"]=
    ID_cprover_string_of_bool_func;
  string_functions["java::java.lang.String.valueOf:(C)Ljava/lang/String;"]=
    ID_cprover_string_of_char_func;
  string_functions["java::java.lang.Integer.parseInt:(Ljava/lang/String;)I"]=
    ID_cprover_string_parse_int_func;

  side_effect_functions
    ["java::java.lang.StringBuilder.append:(Ljava/lang/String;)"
      "Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_func;
  side_effect_functions["java::java.lang.StringBuilder.setCharAt:(IC)V"]=
    ID_cprover_string_char_set_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.append:(I)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_int_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.append:(J)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_long_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.append:(Z)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_bool_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.append:(C)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_char_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.append:(D)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_double_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.append:(F)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_float_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.appendCodePoint:(I)"
     "Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_code_point_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.delete:(II)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_delete_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.deleteCharAt:(I)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_delete_char_at_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(ILjava/lang/String;)"
     "Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(II)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_int_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(IJ)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_long_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(IC)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_char_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(IZ)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_bool_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.setLength:(I)V"]=
    ID_cprover_string_set_length_func;



  side_effect_functions
    ["java::java.lang.StringBuilder.append:([C)"
      "Ljava/lang/StringBuilder;"]=
    ID_cprover_string_concat_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(I[CII)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_func;
  side_effect_functions
    ["java::java.lang.StringBuilder.insert:(I[C)Ljava/lang/StringBuilder;"]=
    ID_cprover_string_insert_func;
    // TODO clean irep ids from insert_char_array etc...

  string_function_calls
    ["java::java.lang.String.<init>:(Ljava/lang/String;)V"]=
    ID_cprover_string_copy_func;
  string_function_calls
    ["java::java.lang.String.<init>:(Ljava/lang/StringBuilder;)V"]=
    ID_cprover_string_copy_func;
  string_function_calls
    ["java::java.lang.StringBuilder.<init>:(Ljava/lang/String;)V"]=
    ID_cprover_string_copy_func;
  string_function_calls["java::java.lang.String.<init>:()V"]=
    ID_cprover_string_empty_string_func;
  string_function_calls["java::java.lang.StringBuilder.<init>:()V"]=
    ID_cprover_string_empty_string_func;

  string_function_calls["java::java.lang.String.<init>:([C)V"]=
    ID_cprover_string_copy_func;
  string_function_calls["java::java.lang.String.<init>:([CII)V"]=
    ID_cprover_string_copy_func;

  string_functions
    ["java::java.lang.String.valueOf:([CII)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  string_functions
    ["java::java.lang.String.valueOf:([C)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  string_functions
    ["java::java.lang.String.copyValueOf:([CII)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;
  string_functions
    ["java::java.lang.String.copyValueOf:([C)Ljava/lang/String;"]=
    ID_cprover_string_copy_func;

  c_string_functions["__CPROVER_uninterpreted_string_literal_func"]=
    ID_cprover_string_literal_func;
  c_string_functions["__CPROVER_uninterpreted_string_char_at_func"]=
    ID_cprover_string_char_at_func;
  c_string_functions["__CPROVER_uninterpreted_string_equal_func"]=
    ID_cprover_string_equal_func;
  c_string_functions["__CPROVER_uninterpreted_string_concat_func"]=
    ID_cprover_string_concat_func;
  c_string_functions["__CPROVER_uninterpreted_string_length_func"]=
    ID_cprover_string_length_func;
  c_string_functions["__CPROVER_uninterpreted_string_substring_func"]=
    ID_cprover_string_substring_func;
  c_string_functions["__CPROVER_uninterpreted_string_is_prefix_func"]=
    ID_cprover_string_is_prefix_func;
  c_string_functions["__CPROVER_uninterpreted_string_is_suffix_func"]=
    ID_cprover_string_is_suffix_func;
  c_string_functions["__CPROVER_uninterpreted_string_contains_func"]=
    ID_cprover_string_contains_func;
  c_string_functions["__CPROVER_uninterpreted_string_index_of_func"]=
    ID_cprover_string_index_of_func;
  c_string_functions["__CPROVER_uninterpreted_string_last_index_of_func"]=
    ID_cprover_string_last_index_of_func;
  c_string_functions["__CPROVER_uninterpreted_string_char_set_func"]=
    ID_cprover_string_char_set_func;
  c_string_functions["__CPROVER_uninterpreted_string_copy_func"]=
    ID_cprover_string_copy_func;
  c_string_functions["__CPROVER_uninterpreted_string_parse_int_func"]=
    ID_cprover_string_parse_int_func;
  c_string_functions["__CPROVER_uninterpreted_string_of_int_func"]=
    ID_cprover_string_of_int_func;

  signatures["java::java.lang.String.equals:(Ljava/lang/Object;)Z"]="SSZ";
  signatures["java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z"]=
    "SSZ";
  signatures["java::java.lang.StringBuilder.insert:(IZ)"
             "Ljava/lang/StringBuilder;"]="SIZS";
  signatures["java::java.lang.StringBuilder.insert:(IJ)"
             "Ljava/lang/StringBuilder;"]="SIJS";
  signatures["java::java.lang.StringBuilder.insert:(II)"
             "Ljava/lang/StringBuilder;"]="SIIS";
  signatures["java::java.lang.StringBuilder.insert:(IC)"
             "Ljava/lang/StringBuilder;"]="SICS";
  signatures["java::java.lang.StringBuilder.insert:(ILjava/lang/String;)"
             "Ljava/lang/StringBuilder;"]="SISS";
  signatures["java::java.lang.StringBuilder.insert:(ILjava/lang/String;)"
             "Ljava/lang/StringBuilder;"]="SISS";
  signatures["java::java.lang.StringBuilder.insert:(I[C)"
             "Ljava/lang/StringBuilder;"]="SI[S";
  signatures["java::java.lang.String.intern:()Ljava/lang/String;"]="SV";
}

/*******************************************************************\

Constructor: string_refine_preprocesst::string_refine_preprocesst

     Inputs: a symbol table, goto functions, a message handler

    Purpose: process the goto function by replacing calls to string functions

\*******************************************************************/

string_refine_preprocesst::string_refine_preprocesst(
  symbol_tablet &_symbol_table,
  goto_functionst &_goto_functions,
  message_handlert &_message_handler):
    messaget(_message_handler),
    ns(_symbol_table),
    symbol_table(_symbol_table),
    goto_functions(_goto_functions),
    next_symbol_id(0),
    jls_ptr(symbol_typet("java::java.lang.String"))
{
  initialize_string_function_table();
  Forall_goto_functions(it, goto_functions)
    replace_string_calls(it);
}
