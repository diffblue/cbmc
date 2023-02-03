/*******************************************************************\

Module: Unit tests of symbol_tablet

Author: Diffblue Ltd.

\*******************************************************************/

/// \file Tests for symbol_tablet

#include <testing-utils/use_catch.h>

#include <util/symbol.h>

SCENARIO(
  "Constructed symbol validity checks",
  "[core][utils][symbol__validity_checks]")
{
  GIVEN("A valid symbol")
  {
    irep_idt symbol_name = "Test_TestBase";
    symbolt symbol{symbol_name, typet{}, ID_C};
    symbol.base_name = "TestBase";
    symbol.module = "TestModule";

    THEN("Symbol should be well formed")
    {
      REQUIRE(symbol.is_well_formed());
    }
  }

  GIVEN("An improperly initialised symbol")
  {
    symbolt symbol;

    WHEN("The symbol doesn't have a valid mode")
    {
      symbol.mode = "";

      THEN("Symbol well-formedness check should fail")
      {
        REQUIRE_FALSE(symbol.is_well_formed());
      }
    }

    WHEN("The symbol doesn't have base name as a suffix to name")
    {
      symbol.name = "TEST";
      symbol.base_name = "TestBase";
      symbol.mode = "C";

      THEN("Symbol well-formedness check should fail")
      {
        REQUIRE_FALSE(symbol.is_well_formed());
      }
    }
  }
}
