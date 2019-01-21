/*******************************************************************\

Module: Unit tests of expression size/offset computation

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

TEST_CASE("Build subexpression to access element at offset into array")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  const signedbv_typet t(32);

  array_typet array_type(t, from_integer(2, size_type()));
  symbol_exprt a("array", array_type);

  {
    const exprt result = get_subexpression_at_offset(a, 0, t, ns);
    REQUIRE(result == index_exprt(a, from_integer(0, index_type())));
  }

  {
    const exprt result = get_subexpression_at_offset(a, 32 / 8, t, ns);
    REQUIRE(result == index_exprt(a, from_integer(1, index_type())));
  }

  {
    const exprt result =
      get_subexpression_at_offset(a, from_integer(0, size_type()), t, ns);
    REQUIRE(result == index_exprt(a, from_integer(0, index_type())));
  }

  {
    const exprt result =
      get_subexpression_at_offset(a, size_of_expr(t, ns), t, ns);
    REQUIRE(result == index_exprt(a, from_integer(1, index_type())));
  }

  {
    const signedbv_typet small_t(8);
    const exprt result = get_subexpression_at_offset(a, 1, small_t, ns);
    REQUIRE(
      result == byte_extract_exprt(
                  byte_extract_id(),
                  index_exprt(a, from_integer(0, index_type())),
                  from_integer(1, index_type()),
                  small_t));
  }
}

TEST_CASE("Build subexpression to access element at offset into struct")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  const signedbv_typet t(32);

  struct_typet st({{"foo", t}, {"bar", t}});

  symbol_exprt s("struct", st);

  {
    const exprt result = get_subexpression_at_offset(s, 0, t, ns);
    REQUIRE(result == member_exprt(s, "foo", t));
  }

  {
    const exprt result = get_subexpression_at_offset(s, 32 / 8, t, ns);
    REQUIRE(result == member_exprt(s, "bar", t));
  }

  {
    const exprt result =
      get_subexpression_at_offset(s, from_integer(0, size_type()), t, ns);
    REQUIRE(result == member_exprt(s, "foo", t));
  }

  {
    const exprt result =
      get_subexpression_at_offset(s, size_of_expr(t, ns), t, ns);
    REQUIRE(result == member_exprt(s, "bar", t));
  }

  {
    const signedbv_typet small_t(8);
    const exprt result = get_subexpression_at_offset(s, 1, small_t, ns);
    REQUIRE(
      result == byte_extract_exprt(
                  byte_extract_id(),
                  member_exprt(s, "foo", t),
                  from_integer(1, index_type()),
                  small_t));
  }
}
