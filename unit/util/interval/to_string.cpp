/*******************************************************************\
 Module: Unit tests for util/interval::to_string
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>

TEST_CASE("interval::to_string", "[core][analyses][interval]")
{
  const signedbv_typet signed_int_type(32);
  const unsignedbv_typet unsigned_int_type(32);
  const auto signed_expr = [&](const int value) {
    return from_integer(value, signed_int_type);
  };
  const auto unsigned_expr = [&](const int value) {
    return from_integer(value, unsigned_int_type);
  };

  REQUIRE(constant_interval_exprt(signed_expr(1)).to_string() == "[1,1]");
  REQUIRE(
    constant_interval_exprt(signed_expr(1), signed_expr(2)).to_string() ==
    "[1,2]");

  REQUIRE(
    constant_interval_exprt::top(signed_int_type).to_string() == "[MIN,MAX]");

  REQUIRE(
    constant_interval_exprt::top(unsigned_int_type).to_string() == "[0,MAX]");

  REQUIRE(
    constant_interval_exprt(signed_expr(1), max_exprt{signed_int_type})
      .to_string() == "[1,MAX]");

  REQUIRE(
    constant_interval_exprt(min_exprt{signed_int_type}, signed_expr(1))
      .to_string() == "[MIN,1]");
  REQUIRE(
    constant_interval_exprt(min_exprt{unsigned_int_type}, unsigned_expr(1))
      .to_string() == "[0,1]");

  REQUIRE(
    constant_interval_exprt(
      min_exprt{signed_int_type}, max_exprt{signed_int_type})
      .to_string() == "[MIN,MAX]");
  REQUIRE(
    constant_interval_exprt(
      min_exprt{unsigned_int_type}, max_exprt{unsigned_int_type})
      .to_string() == "[0,MAX]");
}
