/*******************************************************************\

Module: Statement List Language Type Checking

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Type Checking

#include "statement_list_typecheck.h"

#include <util/ieee_float.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

bool statement_list_typecheck(
  statement_list_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  statement_list_typecheckt stl_typecheck(
    parse_tree, symbol_table, module, message_handler);

  return stl_typecheck.typecheck_main();
}

void statement_list_typecheckt::typecheck()
{
  for(const auto &fn : parse_tree.functions)
  {
    typecheck_function(fn);
  }

  for(const auto &fb : parse_tree.function_blocks)
  {
    typecheck_function_block(fb);
  }
}

void statement_list_typecheckt::typecheck_function_block(
  const statement_list_parse_treet::function_blockt &function_block)
{
  symbolt fb_sym;
  fb_sym.module = module;
  code_typet::parameterst params = typecheck_fb_params(function_block);
  typet return_type(ID_void);
  fb_sym.type = code_typet(params, return_type);
  symbol_table.add(fb_sym);
  typecheck_statement_list_networks(function_block.networks);
  // TODO: Expand function.
  // The complete function body is missing.
}

void statement_list_typecheckt::typecheck_function(
  const statement_list_parse_treet::functiont &function)
{
  // TODO: Implement.
  // This can be done in a similar way as with function blocks. See the Siemens
  // documentation for details about the key differences between functions and
  // function blocks.
  return;
}

code_typet::parameterst statement_list_typecheckt::typecheck_fb_params(
  const statement_list_parse_treet::function_blockt &function_block)
{
  code_typet::parameterst params;

  // Input parameters (read-only, are copied* to the instance data block upon
  // calling it)
  // *TODO: Implement call by reference for structured data types like strings.
  for(const auto &declaration : function_block.var_input)
  {
    typet converted_type =
      typecheck_statement_list_type(declaration.variable.type());
    code_typet::parametert param{converted_type};
    params.push_back(param);
  }

  // Inout parameters (read and write)
  for(const auto &declaration : function_block.var_output)
  {
    typet converted_type =
      typecheck_statement_list_type(declaration.variable.type());
    code_typet::parametert param{converted_type};
    params.push_back(param);
  }

  // Output parameters (write-only, are read by the caller after fb execution)
  for(const auto &declaration : function_block.var_output)
  {
    typet converted_type =
      typecheck_statement_list_type(declaration.variable.type());
    code_typet::parametert param{converted_type};
    params.push_back(param);
  }
  return params;
}

typet statement_list_typecheckt::typecheck_statement_list_type(
  const typet &stl_type)
{
  return std::move(stl_type);
}

void statement_list_typecheckt::typecheck_statement_list_networks(
  const statement_list_parse_treet::networkst &)
{
  // TODO: Implement function.
  // This function should typecheck the instructions in every STL network.
  return;
}
