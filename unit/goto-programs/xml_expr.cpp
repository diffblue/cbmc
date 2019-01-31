/*******************************************************************\

Module: Unit tests of expression to xmlt conversion

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/xml_expr.h>

TEST_CASE("Constant expression to XML")
{
  config.set_arch("none");

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  const constant_exprt number_ubv = from_integer(0xFF, unsignedbv_typet(8));
  const xmlt x_ubv = xml(number_ubv, ns);

  REQUIRE(x_ubv.get_attribute("binary") == "11111111");

  fixedbv_typet fixedbv_type;
  fixedbv_type.set_width(8);
  fixedbv_type.set_integer_bits(6);

  const constant_exprt number_fbv = from_integer(0x3, fixedbv_type);
  const xmlt x_fbv = xml(number_fbv, ns);

  REQUIRE(x_fbv.get_attribute("binary") == "00001100");
}
