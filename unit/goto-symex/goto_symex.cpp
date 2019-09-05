/*******************************************************************\

Module: Unit tests for goto symex

Author: Daniel Poetzl

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <goto-symex/goto_symex.h>
#include <util/ieee_float.h>

#include <iostream>

class goto_symex_testt : public goto_symext
{
  friend void goto_symex_test();
};

void goto_symex_test()
{
  SECTION("get_min_precision()")
  {
    REQUIRE(goto_symex_testt::get_min_precision("12345", "12389") == -2);
    REQUIRE(goto_symex_testt::get_min_precision("123.45", "123.89") == 0);
    REQUIRE(goto_symex_testt::get_min_precision("123.", "123.67") == 0);
    REQUIRE(goto_symex_testt::get_min_precision("123", "123.67") == 0);
    REQUIRE(goto_symex_testt::get_min_precision("123", "123.0056") == 2);

    REQUIRE(goto_symex_testt::get_min_precision("0", "2") == 0);
    REQUIRE(goto_symex_testt::get_min_precision("123.134", "123.345") == 1);
    REQUIRE(goto_symex_testt::get_min_precision("123", "123.0036") == 3);

    REQUIRE(goto_symex_testt::get_min_precision("1.0", "1.1") == 1);
    REQUIRE(goto_symex_testt::get_min_precision("1.0011", "1.0111") == 2);
    REQUIRE(goto_symex_testt::get_min_precision("1.13", "1.16") == 1);
    REQUIRE(goto_symex_testt::get_min_precision("1.09992", "1.10012") == 4);
    REQUIRE(goto_symex_testt::get_min_precision("1.1", "1.100000001") == 9);
    REQUIRE(goto_symex_testt::get_min_precision("1.1000001", "1.2") == 1);
    REQUIRE(goto_symex_testt::get_min_precision("1.", "1.1") == 1);
  }

  SECTION("float_to_java_string()")
  {
    ieee_floatt f(ieee_float_spect::single_precision());

    f.make_NaN();
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "NaN");

    f.make_zero();
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "0.0");

    f.negate();
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "-0.0");

    f.make_plus_infinity();
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "Infinity");

    f.make_minus_infinity();
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "-Infinity");

    f.from_float(123.456);
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "123.456");

    f.from_float(1.25);
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "1.25");

    f.from_float(43479347.4f);
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "4.347935E7");

    f.from_float(-123.456);
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "-123.456");

    f.from_float(-43479347.4f);
    REQUIRE(goto_symex_testt::float_to_java_string(f) == "-4.347935E7");
  }
}

TEST_CASE("", "[core]")
{
  goto_symex_test();
}
