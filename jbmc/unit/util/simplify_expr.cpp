/*******************************************************************\

Module: Unit tests of the expression simplifier

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <java_bytecode/java_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

namespace
{

void test_unnecessary_cast(const typet &type)
{
  config.set_arch("none");

  WHEN("The casts can be removed, they are")
  {
    const exprt simplified=simplify_expr(
      typecast_exprt(
        typecast_exprt(symbol_exprt("foo", type), java_int_type()),
        type),
      namespacet(symbol_tablet()));

    REQUIRE(simplified.id()==ID_symbol);
    REQUIRE(simplified.type()==type);
    const auto &symbol=to_symbol_expr(simplified);
    REQUIRE(symbol.get_identifier()=="foo");
  }

  WHEN("Casts should remain, they are left untouched")
  {
    {
      const exprt simplified=simplify_expr(
        typecast_exprt(symbol_exprt("foo", type), java_int_type()),
        namespacet(symbol_tablet()));

      REQUIRE(simplified.id()==ID_typecast);
      REQUIRE(simplified.type()==java_int_type());
    }

    {
      const exprt simplified=simplify_expr(
        typecast_exprt(symbol_exprt("foo", java_int_type()), type),
        namespacet(symbol_tablet()));

      REQUIRE(simplified.id()==ID_typecast);
      REQUIRE(simplified.type()==type);
    }
  }

  WHEN("Deeply nested casts are present, they are collapsed appropriately")
  {
    {
      const exprt simplified=simplify_expr(
        typecast_exprt(
          typecast_exprt(
            typecast_exprt(
              typecast_exprt(
                typecast_exprt(symbol_exprt("foo", type), java_int_type()),
                type),
              java_int_type()),
            type),
          java_int_type()),
        namespacet(symbol_tablet()));

      REQUIRE(
        simplified==typecast_exprt(symbol_exprt("foo", type), java_int_type()));
    }
  }
}

} // namespace

TEST_CASE("Simplify Java boolean -> int -> boolean casts")
{
  test_unnecessary_cast(java_boolean_type());
}

TEST_CASE("Simplify Java byte -> int -> byte casts")
{
  test_unnecessary_cast(java_byte_type());
}

TEST_CASE("Simplify Java char -> int -> char casts")
{
  test_unnecessary_cast(java_char_type());
}

TEST_CASE("Simplify Java short -> int -> short casts")
{
  test_unnecessary_cast(java_short_type());
}
