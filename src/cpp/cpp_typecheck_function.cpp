/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <i2string.h>
#include <identifier.h>
#include <ansi-c/c_qualifiers.h>
#include <expr_util.h>

#include "cpp_template_type.h"
#include "cpp_typecheck.h"
#include "cpp_type2name.h"
#include "cpp_util.h"

/*******************************************************************\

Function: cpp_typecheckt::convert_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_argument(
  const irep_idt &mode,
  code_typet::argumentt &argument)
{
  std::string identifier=id2string(argument.get_identifier());

  if(identifier.empty())
  {
    identifier="#anon_arg"+i2string(anon_counter++);
    argument.set_base_name(identifier);
  }

  identifier=cpp_identifier_prefix(mode)+"::"+
             cpp_scopes.current_scope().prefix+
             id2string(identifier);

  argument.set_identifier(identifier);

  symbolt symbol;

  symbol.name=identifier;
  symbol.base_name=argument.get_base_name();
  symbol.location=argument.location();
  symbol.mode=mode;
  symbol.module=module;
  symbol.type=argument.type();
  symbol.is_statevar=true;
  symbol.lvalue=!is_reference(symbol.type);

  assert(!symbol.base_name.empty());

  symbolt *new_symbol;

  if(context.move(symbol, new_symbol))
  {
    err_location(symbol.location);
    str << "cpp_typecheckt::convert_argument: context.move("
        << symbol.name << ") failed";
    throw 0;
  }

  // put into scope
  cpp_scopes.put_into_scope(*new_symbol);
}

/*******************************************************************\

Function: cpp_typecheckt::convert_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_arguments(
  const irep_idt &mode,
  code_typet &function_type)
{
  code_typet::argumentst &arguments=
    function_type.arguments();

  for(code_typet::argumentst::iterator
      it=arguments.begin();
      it!=arguments.end();
      it++)
    convert_argument(mode, *it);
}

/*******************************************************************\

Function: cpp_typecheckt::convert_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_function(symbolt &symbol)
{
  code_typet &function_type=
    to_code_type(template_subtype(symbol.type));

  // only a prototype?
  if(symbol.value.is_nil())
    return;

  // if it is a destructor, add the implicit code
  if(symbol.type.get(ID_return_type)==ID_destructor)
  {
    const symbolt &msymb=lookup(symbol.type.get("#member_name"));

    assert(symbol.value.id()==ID_code);
    assert(symbol.value.get(ID_statement)==ID_block);

    symbol.value.copy_to_operands(dtor(msymb));
  }

  // enter appropriate scope
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopet &function_scope=cpp_scopes.set_scope(symbol.name);

  // fix the scope's prefix
  function_scope.prefix+=id2string(symbol.name)+"::";

  // genuine function definition -- do the parameter declarations
  convert_arguments(symbol.mode, function_type);

  // create "this" if it's a non-static method
  if(function_scope.is_method &&
     !function_scope.is_static_member)
  {
    code_typet::argumentst &arguments=function_type.arguments();
    assert(arguments.size()>=1);
    code_typet::argumentt &this_argument_expr=arguments.front();
    function_scope.this_expr=exprt(ID_symbol, this_argument_expr.type());
    function_scope.this_expr.set(ID_identifier, this_argument_expr.get(ID_C_identifier));
  }
  else
    function_scope.this_expr.make_nil();

  // do the function body
  start_typecheck_code();

  // save current return type
  typet old_return_type = return_type;

  return_type=function_type.return_type();
  typecheck_code(to_code(symbol.value));

  symbol.value.type()=symbol.type;
  
  return_type = old_return_type;
}

/*******************************************************************\

Function: cpp_typecheckt::function_identifier

  Inputs:

 Outputs:

 Purpose: for function overloading

\*******************************************************************/

irep_idt cpp_typecheckt::function_identifier(const typet &type)
{
  const code_typet &function_type=
    to_code_type(template_subtype(type));

  const code_typet::argumentst &arguments=
    function_type.arguments();

  std::string result;
  bool first=true;

  result+='(';

  // the name of the function should not depend on
  // the class name that is encoded in the type of this,
  // but we must distinguish "const" and "non-const" member
  // functions

  code_typet::argumentst::const_iterator it=
    arguments.begin();

  if(it!=arguments.end() &&
     it->get_identifier()==ID_this)
  {
    const typet &pointer=it->type();
    const typet &symbol =pointer.subtype();
    if(symbol.get_bool(ID_C_constant)) result+="const$";
    result+="this";
    first=false;
    it++;
  }

  // we skipped the "this", on purpose!

  for(; it!=arguments.end(); it++)
  {
    if(first) first=false; else result+=",";
    typet tmp_type=it->type();
    result+=cpp_type2name(it->type());
  }

  result+=')';

  return result;
}
