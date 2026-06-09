/*******************************************************************\

 Module: Unit tests for string_literal_length

 Author: Michael Tautschnig

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <testing-utils/use_catch.h>

TEST_CASE("string_literal_length", "[core][util][string_constant]")
{
  // string_constantt::make_type uses char_type()/c_index_type(), which require
  // a configured architecture.
  cmdlinet cmdline;
  config.set(cmdline);

  // Build the offset-`offset` decay of a string literal: &literal[offset].
  const auto decay = [](const irep_idt &value, const mp_integer &offset)
  {
    return address_of_exprt{index_exprt{
      string_constantt{value}, from_integer(offset, c_index_type())}};
  };

  SECTION("empty literal folds to 0")
  {
    REQUIRE(string_literal_length(decay("", 0)) == 0);
  }
  SECTION("single character folds to 1")
  {
    REQUIRE(string_literal_length(decay("a", 0)) == 1);
  }
  SECTION("length is counted up to the first embedded NUL")
  {
    REQUIRE(string_literal_length(decay(std::string{"a\0b", 3}, 0)) == 1);
  }
  SECTION("multi-character literal folds to its length")
  {
    REQUIRE(string_literal_length(decay("hello", 0)) == 5);
  }
  SECTION("typecasts around the literal are peeled")
  {
    const exprt arg =
      typecast_exprt{decay("hello", 0), pointer_type(char_type())};
    REQUIRE(string_literal_length(arg) == 5);
  }
  SECTION("a constant offset into the literal folds")
  {
    REQUIRE(string_literal_length(decay("hello", 2)) == 3);
    REQUIRE(string_literal_length(decay("hello", 5)) == 0);
    REQUIRE(string_literal_length(decay(std::string{"a\0bc", 4}, 2)) == 2);
  }
  SECTION("an offset beyond the terminating NUL does not fold")
  {
    REQUIRE_FALSE(string_literal_length(decay("hello", 6)).has_value());
  }
  SECTION("adding a constant to the literal folds")
  {
    const plus_exprt sum{decay("hello", 1), from_integer(2, c_index_type())};
    REQUIRE(string_literal_length(sum) == 2);
  }
  SECTION("adding a non-constant to the literal does not fold")
  {
    const plus_exprt sum{decay("hello", 0), symbol_exprt{"i", c_index_type()}};
    REQUIRE_FALSE(string_literal_length(sum).has_value());
  }
  SECTION("a non-literal argument does not fold")
  {
    REQUIRE_FALSE(
      string_literal_length(symbol_exprt{"p", pointer_type(char_type())})
        .has_value());
  }
  SECTION("a conditional between literals does not fold")
  {
    const if_exprt cond{
      symbol_exprt{"c", bool_typet{}}, decay("ab", 0), decay("cdef", 0)};
    REQUIRE_FALSE(string_literal_length(cond).has_value());
  }
}
