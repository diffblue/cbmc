/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/c_types.h>

#include "cpp_template_type.h"
#include "cpp_type2name.h"

void cpp_typecheckt::convert_parameter(
  const irep_idt &current_mode,
  code_typet::parametert &parameter)
{
  irep_idt base_name=id2string(parameter.get_base_name());

  if(base_name.empty())
  {
    base_name="#anon_arg"+std::to_string(anon_counter++);
    parameter.set_base_name(base_name);
  }

  PRECONDITION(!cpp_scopes.current_scope().prefix.empty());
  irep_idt identifier=cpp_scopes.current_scope().prefix+
                      id2string(base_name);

  parameter.set_identifier(identifier);

  // the parameter may already have been set up if dealing with virtual methods
  const symbolt *check_symbol;
  if(!lookup(identifier, check_symbol))
    return;

  parameter_symbolt symbol;

  symbol.name=identifier;
  symbol.base_name=parameter.get_base_name();
  symbol.location=parameter.source_location();
  symbol.mode = current_mode;
  symbol.module=module;
  symbol.type=parameter.type();
  symbol.is_lvalue=!is_reference(symbol.type);

  INVARIANT(!symbol.base_name.empty(), "parameter has base name");

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::convert_parameter: symbol_table.move(\""
            << symbol.name << "\") failed" << eom;
    throw 0;
  }

  // put into scope
  cpp_scopes.put_into_scope(*new_symbol);
}

void cpp_typecheckt::convert_parameters(
  const irep_idt &current_mode,
  code_typet &function_type)
{
  code_typet::parameterst &parameters=
    function_type.parameters();

  for(code_typet::parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
    convert_parameter(current_mode, *it);
}

void cpp_typecheckt::convert_function(symbolt &symbol)
{
  code_typet &function_type=
    to_code_type(template_subtype(symbol.type));

  // only a prototype?
  if(symbol.value.is_nil())
    return;

  if(symbol.value.id() != ID_code)
  {
    error().source_location = symbol.location;
    error() << "function '" << symbol.name << "' is initialized with "
            << symbol.value.id() << eom;
    throw 0;
  }

  // enter appropriate scope
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopet &function_scope=cpp_scopes.set_scope(symbol.name);

  // fix the scope's prefix
  function_scope.prefix=id2string(symbol.name)+"::";

  // genuine function definition -- do the parameter declarations
  convert_parameters(symbol.mode, function_type);

  // create "this" if it's a non-static method
  if(function_scope.is_method &&
     !function_scope.is_static_member)
  {
    code_typet::parameterst &parameters=function_type.parameters();
    assert(parameters.size()>=1);
    code_typet::parametert &this_parameter_expr=parameters.front();
    function_scope.this_expr = symbol_exprt{
      this_parameter_expr.get_identifier(), this_parameter_expr.type()};
  }
  else
    function_scope.this_expr.make_nil();

  // if it is a destructor, add the implicit code
  if(to_code_type(symbol.type).return_type().id() == ID_destructor)
  {
    const symbolt &msymb = lookup(symbol.type.get(ID_C_member_name));

    PRECONDITION(symbol.value.id() == ID_code);
    PRECONDITION(symbol.value.get(ID_statement) == ID_block);

    if(
      !symbol.value.has_operands() ||
      !to_multi_ary_expr(symbol.value).op0().has_operands() ||
      to_multi_ary_expr(to_multi_ary_expr(symbol.value).op0()).op0().id() !=
        ID_already_typechecked)
    {
      symbol.value.copy_to_operands(
        dtor(msymb, to_symbol_expr(function_scope.this_expr)));
    }
  }

  // do the function body
  start_typecheck_code();

  // save current return type
  typet old_return_type=return_type;

  return_type=function_type.return_type();

  // constructor, destructor?
  if(return_type.id() == ID_constructor || return_type.id() == ID_destructor)
    return_type = void_type();

  typecheck_code(to_code(symbol.value));

  symbol.value.type()=symbol.type;

  return_type = old_return_type;

  deferred_typechecking.erase(symbol.name);
}

/// for function overloading
irep_idt cpp_typecheckt::function_identifier(const typet &type)
{
  const code_typet &function_type=
    to_code_type(template_subtype(type));

  const code_typet::parameterst &parameters=
    function_type.parameters();

  std::string result;
  bool first=true;

  result+='(';

  // the name of the function should not depend on
  // the class name that is encoded in the type of this,
  // but we must distinguish "const" and "non-const" member
  // functions

  code_typet::parameterst::const_iterator it=
    parameters.begin();

  if(it != parameters.end() && it->get_this())
  {
    const typet &pointer=it->type();
    const typet &symbol = to_pointer_type(pointer).base_type();
    if(symbol.get_bool(ID_C_constant))
      result += "$const";
    if(symbol.get_bool(ID_C_volatile))
      result += "$volatile";
    result += id2string(ID_this);
    first=false;
    it++;
  }

  // we skipped the "this", on purpose!

  for(; it!=parameters.end(); it++)
  {
    if(first)
      first=false;
    else
      result+=',';
    typet tmp_type=it->type();
    result+=cpp_type2name(it->type());
  }

  result+=')';

  return result;
}
