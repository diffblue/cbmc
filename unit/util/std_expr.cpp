/*******************************************************************\

Module: Unit test for std_expr.h/std_expr.cpp

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

TEST_CASE("for a division expression...", "[unit][util][std_expr]")
{
  auto dividend = from_integer(10, integer_typet());
  auto divisor = from_integer(5, integer_typet());
  auto div = div_exprt(dividend, divisor);

  SECTION("its divisor and dividend have the values assigned to them")
  {
    REQUIRE(div.dividend() == dividend);
    REQUIRE(div.divisor() == divisor);
  }

  SECTION("its type is that of its operands")
  {
    REQUIRE(div.type() == integer_typet());
  }
}

TEST_CASE("object descriptor expression", "[unit][util][std_expr]")
{
  config.ansi_c.set_LP64();

  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  array_typet array_type(signed_int_type(), from_integer(2, size_type()));
  struct_typet struct_type({{"foo", array_type}});

  SECTION("object descriptors of index expressions")
  {
    const symbol_exprt s("array", array_type);
    // s[1]
    const index_exprt index(s, from_integer(1, c_index_type()));

    object_descriptor_exprt ode;
    ode.build(index, ns);
    REQUIRE(ode.root_object() == s);
    // in LP64 a signed int is 4 bytes
    REQUIRE(simplify_expr(ode.offset(), ns) == from_integer(4, c_index_type()));
  }

  SECTION("object descriptors of member expressions")
  {
    const symbol_exprt s("struct", struct_type);
    // s.foo
    const member_exprt member(s, "foo", array_type);
    // s.foo[1]
    const index_exprt index(member, from_integer(1, c_index_type()));

    object_descriptor_exprt ode;
    ode.build(index, ns);
    REQUIRE(ode.root_object() == s);
    // in LP64 a signed int is 4 bytes
    REQUIRE(simplify_expr(ode.offset(), ns) == from_integer(4, c_index_type()));
  }
}
