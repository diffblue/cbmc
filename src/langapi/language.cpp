/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#include "language.h"

#include <util/expr.h>
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/std_types.h>

bool languaget::final(symbol_table_baset &)
{
  return false;
}

bool languaget::interfaces(symbol_tablet &)
{
  return false;
}

void languaget::dependencies(
  const std::string &,
  std::set<std::string> &)
{
}

bool languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &)
{
  code=expr.pretty();
  return false;
}

bool languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &)
{
  code=type.pretty();
  return false;
}

bool languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &)
{
  // probably ansi-c/type2name could be used as better fallback if moved to
  // util/
  name=type.pretty();
  return false;
}

/// Turn on or off stub generation.
/// \param should_generate_stubs: Should stub generation be enabled
void languaget::set_should_generate_opaque_method_stubs(
  bool should_generate_stubs)
{
  generate_opaque_stubs=should_generate_stubs;
}

/// When there are opaque methods (e.g. ones where we don't have a body), we
/// create a stub function in the goto program and mark it as opaque so the
/// interpreter fills in appropriate values for it. This will only happen if
/// generate_opaque_stubs is enabled.
/// \param symbol_table: the symbol table for the program
void languaget::generate_opaque_method_stubs(symbol_tablet &symbol_table)
{
  if(generate_opaque_stubs)
  {
    system_symbols=system_library_symbolst();

    for(auto &symbol_entry : symbol_table.symbols)
    {
      if(is_symbol_opaque_function(symbol_entry.second))
      {
        symbolt &symbol=
          *symbol_table.get_writeable(symbol_entry.second.name);

        generate_opaque_parameter_symbols(symbol, symbol_table);

        irep_idt return_symbol_id=generate_opaque_stub_body(
          symbol,
          symbol_table);

        if(return_symbol_id!=ID_nil)
        {
          symbol.type.set("opaque_method_capture_symbol", return_symbol_id);
        }
      }
    }
  }
}

/// To generate the stub function for the opaque function in question. The
/// identifier is used in the flag to the interpreter that the function is
/// opaque. This function should be implemented in the languages.
/// \param symbol: the function symbol which is opaque
/// \param symbol_table: the symbol table
/// \return The identifier of the return variable. ID_nil if the function
///   doesn't return anything.
irep_idt languaget::generate_opaque_stub_body(
  symbolt &symbol,
  symbol_tablet &symbol_table)
{
  // unused parameters
  (void)symbol;
  (void)symbol_table;
  return ID_nil;
}

/// To build the parameter symbol and choose its name. This should be
/// implemented in each language.
/// \param function_symbol: the symbol of an opaque function
/// \param parameter_index: the index of the parameter within the the parameter
///   list
/// \param parameter_type: the type of the parameter
/// \return A named symbol to be added to the symbol table representing one of
///   the parameters in this opaque function.
parameter_symbolt languaget::build_stub_parameter_symbol(
  const symbolt &function_symbol,
  size_t parameter_index,
  const code_typet::parametert &parameter)
{
  // unused parameters
  (void)function_symbol;
  (void)parameter_index;
  (void)parameter;
  error() << "language " << id()
          << " doesn't implement build_stub_parameter_symbol. "
          << "This means cannot use opaque functions." << eom;

  return parameter_symbolt();
}

/// To get the name of the symbol to be used for the return value of the
/// function. Generates a name like to_return_function_name
/// \param function_id: the function that has a return value
/// \return the identifier to use for the symbol that will store the return
///   value of this function.
irep_idt languaget::get_stub_return_symbol_name(const irep_idt &function_id)
{
  std::ostringstream return_symbol_name_builder;
  return_symbol_name_builder << "to_return_" << function_id;
  return return_symbol_name_builder.str();
}


/// To identify if a given symbol is an opaque function and hence needs to be
/// stubbed. We explicitly exclude CPROVER functions, if they have no body it is
/// because we haven't generated it yet.
/// \param symbol: the symbol to be checked
/// \return True if the symbol is an opaque (e.g. non-bodied) function
bool languaget::is_symbol_opaque_function(const symbolt &symbol)
{
  std::set<std::string> headers;
  // Don't create stubs for symbols like:
  // __CPROVER_blah (which aren't real external functions)
  // and strstr (which we will model for ourselves later)
  bool is_internal=system_symbols.is_symbol_internal_symbol(symbol, headers);

  return !symbol.is_type &&
    symbol.value.id()==ID_nil &&
    symbol.type.id()==ID_code &&
    !is_internal;
}

/// To create stub parameter symbols for each parameter the function has and
/// assign their IDs into the parameters identifier.
/// \param function_symbol: the symbol of an opaque function
/// \param symbol_table: the symbol table to add the new parameter symbols into
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
