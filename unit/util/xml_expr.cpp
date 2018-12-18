/*******************************************************************\

 Module: Unit tests of expression to xmlt conversion

 Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/xml_expr.h>

TEST_CASE("Constant expression to XML")
{
  config.set_arch("none");

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  const constant_exprt number = from_integer(0xFF, unsignedbv_typet(8));
  const xmlt x = xml(number, ns);

  REQUIRE(x.get_attribute("binary") == "11111111");
}
