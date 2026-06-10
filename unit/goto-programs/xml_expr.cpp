/*******************************************************************\

Module: Unit tests of expression to xmlt conversion

Author: Michael Tautschnig

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/namespace.h>

#include <goto-programs/xml_expr.h>

#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Constant expression to XML")
{
  config.set_arch("none");

  const constant_exprt number_ubv = from_integer(0xFF, unsignedbv_typet(8));
  const xmlt x_ubv = xml(number_ubv, empty_namespace);

  REQUIRE(x_ubv.get_attribute("binary") == "11111111");

  fixedbv_typet fixedbv_type;
  fixedbv_type.set_width(8);
  fixedbv_type.set_integer_bits(6);

  const constant_exprt number_fbv = from_integer(0x3, fixedbv_type);
  const xmlt x_fbv = xml(number_fbv, empty_namespace);

  REQUIRE(x_fbv.get_attribute("binary") == "00001100");
}
