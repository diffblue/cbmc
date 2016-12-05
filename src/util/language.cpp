/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language.h"
#include "expr.h"
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/std_types.h>

/*******************************************************************\

Function: languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::final(symbol_tablet &symbol_table)
{
  return false;
}

/*******************************************************************\

Function: languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::interfaces(symbol_tablet &symbol_table)
{
  return false;
}

/*******************************************************************\

Function: languaget::dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void languaget::dependencies(
  const std::string &module,
  std::set<std::string> &modules)
{
}

/*******************************************************************\

Function: languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr.pretty();
  return false;
}

/*******************************************************************\

Function: languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type.pretty();
  return false;
}

/*******************************************************************\

Function: languaget::type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  // probably ansi-c/type2name could be used as better fallback if moved to
  // util/
  name=type.pretty();
  return false;
}

/*******************************************************************\

Function: languaget::generate_opaque_method_stubs

  Inputs:
          symbol_table - the symbol table for the program

 Outputs:

 Purpose: When there are opaque methods (e.g. ones where we don't
          have a body), we create a stub function in the goto
          program and mark it as opaque so the interpreter fills in
          appropriate values for it.

\*******************************************************************/

void languaget::generate_opaque_method_stubs(symbol_tablet &symbol_table)
{
  for(auto &symbol_entry : symbol_table.symbols)
  {
    if(is_symbol_opaque_function(symbol_entry.second))
    {
      symbolt &symbol=symbol_entry.second;

      generate_opaque_parameter_symbols(symbol, symbol_table);

      irep_idt return_symbol_id = generate_opaque_stub_body(
        symbol,
        symbol_table);

      if(return_symbol_id!=ID_nil)
      {
        symbol.type.set("opaque_method_capture_symbol", return_symbol_id);
      }
    }
  }
}

/*******************************************************************\

Function: languaget::generate_opaque_stub_body

  Inputs:
          symbol - the function symbol which is opaque
          symbol_table - the symbol table

 Outputs: The identifier of the return variable. ID_nil if the function
          doesn't return anything.

 Purpose: To generate the stub function for the opaque function in
          question. The identifier is used in the flag to the interpreter
          that the function is opaque. This function should be implemented
          in the languages.

\*******************************************************************/

irep_idt languaget::generate_opaque_stub_body(
  symbolt &symbol,
  symbol_tablet &symbol_table)
{
  return ID_nil;
}

/*******************************************************************\

Function: languaget::build_stub_parameter_symbol

  Inputs:
          function_symbol - the symbol of an opaque function
          parameter_index - the index of the parameter within the
                            the parameter list
          parameter_type - the type of the parameter

 Outputs: A named symbol to be added to the symbol table representing
          one of the parameters in this opaque function.

 Purpose: To build the parameter symbol and choose its name. This should
          be implemented in each language.

\*******************************************************************/

parameter_symbolt languaget::build_stub_parameter_symbol(
  const symbolt &function_symbol,
  size_t parameter_index,
  const code_typet::parametert &parameter)
{
  error() << "language " << id()
          << " doesn't implement build_stub_parameter_symbol. "
          << "This means cannot use opaque functions." << eom;

  return parameter_symbolt();
}

/*******************************************************************\

Function: languaget::get_stub_return_symbol_name

  Inputs:
          function_id - the function that has a return value

 Outputs: the identifier to use for the symbol that will store the
          return value of this function.

 Purpose: To get the name of the symbol to be used for the return value
          of the function. Generates a name like to_return_function_name

\*******************************************************************/

irep_idt languaget::get_stub_return_symbol_name(const irep_idt &function_id)
{
  std::ostringstream return_symbol_name_builder;
  return_symbol_name_builder << "to_return_" << function_id;
  return return_symbol_name_builder.str();
}


/*******************************************************************\

Function: languaget::is_symbol_opaque_function

  Inputs:
          symbol - the symbol to be checked

 Outputs: True if the symbol is an opaque (e.g. non-bodied) function

 Purpose: To identify if a given symbol is an opaque function and
          hence needs to be stubbed. We explicitly exclude CPROVER
          functions, if they have no body it is because we haven't
          generated it yet.

\*******************************************************************/

bool languaget::is_symbol_opaque_function(const symbolt &symbol)
{
  // Explictly exclude CPROVER functions since these aren't opaque
  std::string variable_id_str(symbol.name.c_str());
  bool is_cprover_function = has_prefix(variable_id_str, CPROVER_PREFIX);

  return !symbol.is_type &&
    symbol.value.id()==ID_nil &&
    symbol.type.id()==ID_code &&
    !is_cprover_function;
}

/*******************************************************************\

Function: languaget::generate_opaque_parameter_symbols

  Inputs:
          function_symbol - the symbol of an opaque function
          symbol_table - the symbol table to add the new parameter
                         symbols into

 Outputs:

 Purpose: To create stub parameter symbols for each parameter the
          function has and assign their IDs into the parameters
          identifier.

\*******************************************************************/

void languaget::generate_opaque_parameter_symbols(
  symbolt &function_symbol,
  symbol_tablet &symbol_table)
{
  code_typet &function_type = to_code_type(function_symbol.type);
  code_typet::parameterst &parameters=function_type.parameters();
  for(std::size_t i=0; i<parameters.size(); ++i)
  {
    code_typet::parametert &param=parameters[i];
    const parameter_symbolt &param_symbol=
      build_stub_parameter_symbol(function_symbol, i, param);

    param.set_base_name(param_symbol.base_name);
    param.set_identifier(param_symbol.name);

    symbol_table.add(param_symbol);
  }
}
