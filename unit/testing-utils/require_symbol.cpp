/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Limited.

\*******************************************************************/

#include "require_symbol.h"
#include "catch.hpp"

/// Verify whether a given identifier is found in the symbol table and return it
/// \param symbol_table: The symbol table to look in
/// \param symbol_identifier: The name of the symbol
const symbolt &require_symbol::require_symbol_exists(
  const symbol_tablet &symbol_table,
  const irep_idt &symbol_identifier)
{
  const symbolt *found_symbol = symbol_table.lookup(symbol_identifier);
  INFO("Looking for symbol: " + id2string(symbol_identifier));
  REQUIRE(found_symbol != nullptr);
  return *found_symbol;
}
