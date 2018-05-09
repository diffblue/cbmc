/*******************************************************************\

Module: ANSI-C Language Frontend

Author: Daniel Kroening

\*******************************************************************/

#include <exception>

#include "ansi_c_frontend.h"

const goto_functiont &&
ansi_c_frontendt::make_function(const irep_idt &identifier)
{
  goto_functiont f;
  return std::move(f);
}

const symbolt &ansi_c_frontendt::get_symbol(const irep_idt &identifier)
{
  auto s_it = symbol_table.symbols.find(identifier);
  if(s_it == symbol_table.symbols.end())
    throw std::invalid_argument("symbol not found");

  return s_it->second;
}
