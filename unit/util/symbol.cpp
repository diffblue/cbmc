/*******************************************************************\

Module: Unit tests of symbol_tablet

Author: Diffblue Ltd.

\*******************************************************************/

/// \file Tests for symbol_tablet

#include <testing-utils/catch.hpp>
#include <util/exception_utils.h>
#include <util/symbol.h>

SCENARIO(
  "Constructed symbol validity checks",
  "[core][utils][symbol__validity_checks]")
{
  GIVEN("A valid symbol")
  {
    symbolt symbol;
    irep_idt symbol_name = "Test_TestBase";
    symbol.name = symbol_name;
    symbol.base_name = "TestBase";
    symbol.module = "TestModule";
    symbol.mode = "C";

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
