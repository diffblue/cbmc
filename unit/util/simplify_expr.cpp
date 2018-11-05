/*******************************************************************\

 Module: Unit tests of the expression simplifier

 Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

TEST_CASE("Simplify pointer_offset(address of array index)")
{
  config.set_arch("none");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  array_typet array_type(char_type(), from_integer(2, size_type()));
  symbol_exprt array("A", array_type);
  index_exprt index(array, from_integer(1, index_type()));
  address_of_exprt address_of(index);

  exprt p_o=pointer_offset(address_of);

  exprt simp=simplify_expr(p_o, ns);

  REQUIRE(simp.id()==ID_constant);
  const mp_integer offset_value = numeric_cast_v<mp_integer>(simp);
  REQUIRE(offset_value==1);
}

TEST_CASE("Simplify const pointer offset")
{
  config.set_arch("none");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  // build a numeric constant of some pointer type
  constant_exprt number=from_integer(1234, size_type());
  number.type()=pointer_type(char_type());

  exprt p_o=pointer_offset(number);

  exprt simp=simplify_expr(p_o, ns);

  REQUIRE(simp.id()==ID_constant);
  const mp_integer offset_value = numeric_cast_v<mp_integer>(simp);
  REQUIRE(offset_value==1234);
}

TEST_CASE("Simplify byte extract")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  // byte-extracting type T at offset 0 from an object of type T yields the
  // object
  symbol_exprt s("foo", size_type());
  byte_extract_exprt be(
    byte_extract_id(), s, from_integer(0, index_type()), size_type());

  exprt simp = simplify_expr(be, ns);

  REQUIRE(simp == s);
}
