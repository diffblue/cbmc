/*******************************************************************\

 Module: Code Observer Tests.

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Unit tests for code_observer.h

#include <testing-utils/catch.hpp>
#include <util/std_types.h>
#include <util/symbol_table.h>
#include <util/code_observer.h>

// Utilities

static void add_codet(
  const exprt &value,
  const std::string &name,
  symbol_tablet &symbol_table)
{
  symbolt new_symbol;
  new_symbol.name = name;
  new_symbol.type = code_typet();
  new_symbol.value = value;
  symbol_table.add(new_symbol);
}

// Observers

static void count_skips(const codet &code, int &count)
{
  REQUIRE(code.id() == ID_code);
  REQUIRE(code.get_statement() == ID_skip);
  ++count;
}

// Tests

TEST_CASE("Count number of codet(ID_SKIP)")
{
  symbol_tablet symbol_table;
  add_codet(codet(ID_skip), "SKIP1", symbol_table);
  add_codet(codet(ID_decl), "DECL", symbol_table);
  add_codet(codet(ID_skip), "SKIP2", symbol_table);

  int count = 0;
  const_code_observert code_observer;
  code_observer.register_observer(
    ID_skip, &count_skips, std::placeholders::_1, std::ref(count));
  code_observer.visit_symbols(symbol_table);

  REQUIRE(count == 2);
}
