/******************************************************************\

Module: help formatter unit tests

Author: Michael Tautschnig

\******************************************************************/

#include <util/help_formatter.h>

#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE("help_formatter", "[core][util]")
{
  std::ostringstream oss;
  oss.clear();
  oss << help_formatter("--abc \t xyz\n");
  REQUIRE(oss.str() == "--abc                         xyz\n");
}
