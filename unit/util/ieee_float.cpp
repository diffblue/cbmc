/*******************************************************************\

Module: Unit tests for util/ieee_float

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/ieee_float.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>

#include <limits>

TEST_CASE("Make an IEEE 754 one", "[core][util][ieee_float]")
{
  auto spec = ieee_float_spect::single_precision();
  REQUIRE(ieee_floatt::one(spec) == 1);
}

TEST_CASE("round_to_integral", "[unit][util][ieee_float]")
{
  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };

  auto round_to_integral =
    [](ieee_float_valuet op, ieee_floatt::rounding_modet rm) {
      return ieee_floatt{op, rm}.round_to_integral();
    };

  const auto dp = ieee_float_spect::double_precision();

  const auto NaN = ieee_float_valuet::NaN(dp);
  const auto plus_inf = ieee_float_valuet::plus_infinity(dp);
  const auto minus_inf = ieee_float_valuet::minus_infinity(dp);
  const auto dmax = std::numeric_limits<double>::max();

  const auto up = ieee_floatt::ROUND_TO_PLUS_INF;

  REQUIRE(round_to_integral(NaN, up) == NaN);
  REQUIRE(round_to_integral(plus_inf, up) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, up) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), up) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), up) == -0.0);
  REQUIRE(round_to_integral(from_double(1), up) == 1);
  REQUIRE(round_to_integral(from_double(0.1), up) == 1);
  REQUIRE(round_to_integral(from_double(-0.1), up) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), up) == 1);
  REQUIRE(round_to_integral(from_double(0.49999999), up) == 1);
  REQUIRE(round_to_integral(from_double(0.500000001), up) == 1);
  REQUIRE(round_to_integral(from_double(10.1), up) == 11);
  REQUIRE(round_to_integral(from_double(-10.1), up) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), up) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), up) == dmax);

  const auto down = ieee_floatt::ROUND_TO_MINUS_INF;

  REQUIRE(round_to_integral(NaN, down) == NaN);
  REQUIRE(round_to_integral(plus_inf, down) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, down) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), down) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), down) == -0.0);
  REQUIRE(round_to_integral(from_double(1), down) == 1);
  REQUIRE(round_to_integral(from_double(0.1), down) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), down) == -1);
  REQUIRE(round_to_integral(from_double(0.5), down) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), down) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), down) == 0);
  REQUIRE(round_to_integral(from_double(10.1), down) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), down) == -11);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), down) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), down) == dmax);

  const auto even = ieee_floatt::ROUND_TO_EVEN;

  REQUIRE(round_to_integral(NaN, even) == NaN);
  REQUIRE(round_to_integral(plus_inf, even) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, even) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), even) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), even) == -0.0);
  REQUIRE(round_to_integral(from_double(1), even) == 1);
  REQUIRE(round_to_integral(from_double(0.1), even) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), even) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), even) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), even) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), even) == 1);
  REQUIRE(round_to_integral(from_double(10.1), even) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), even) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), even) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), even) == dmax);

  const auto zero = ieee_floatt::ROUND_TO_ZERO;

  REQUIRE(round_to_integral(NaN, zero) == NaN);
  REQUIRE(round_to_integral(plus_inf, zero) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, zero) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), zero) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), zero) == -0.0);
  REQUIRE(round_to_integral(from_double(1), zero) == 1);
  REQUIRE(round_to_integral(from_double(0.1), zero) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), zero) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), zero) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), zero) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), zero) == 0);
  REQUIRE(round_to_integral(from_double(10.1), zero) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), zero) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), zero) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), zero) == dmax);

  const auto away = ieee_floatt::ROUND_TO_AWAY;

  REQUIRE(round_to_integral(NaN, away) == NaN);
  REQUIRE(round_to_integral(plus_inf, away) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, away) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), away) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), away) == -0.0);
  REQUIRE(round_to_integral(from_double(1), away) == 1);
  REQUIRE(round_to_integral(from_double(0.1), away) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), away) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), away) == 1);
  REQUIRE(round_to_integral(from_double(0.49999999), away) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), away) == 1);
  REQUIRE(round_to_integral(from_double(10.1), away) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), away) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), away) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), away) == dmax);
}

TEST_CASE("ieee signbit / fabs / copysign", "[core][util][ieee_float]")
{
  const auto dp = ieee_float_spect::double_precision();
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  // Build a double-precision floating-point constant expression.
  auto fc = [&](double d) -> exprt
  {
    ieee_floatt v{dp, ieee_floatt::rounding_modet::ROUND_TO_EVEN};
    v.from_double(d);
    return v.to_expr();
  };
  // Evaluate a float-valued expression to a double via simplification.
  auto eval = [&](const exprt &e) -> double
  {
    exprt s = simplify_expr(e, ns);
    REQUIRE(s.is_constant());
    ieee_float_valuet v{to_constant_expr(s)};
    return v.to_double();
  };
  auto eval_bool = [&](const exprt &e) -> bool
  { return simplify_expr(e, ns).is_true(); };

  SECTION("signbit reflects the sign BIT, not ordering")
  {
    REQUIRE(eval_bool(ieee_signbit(fc(-0.0))));      // negative zero
    REQUIRE_FALSE(eval_bool(ieee_signbit(fc(0.0)))); // positive zero
    REQUIRE(eval_bool(ieee_signbit(fc(-3.5))));
    REQUIRE_FALSE(eval_bool(ieee_signbit(fc(3.5))));
  }

  SECTION("fabs clears the sign bit, incl. negative zero")
  {
    REQUIRE(eval(ieee_fabs(fc(-3.5))) == 3.5);
    REQUIRE(eval(ieee_fabs(fc(3.5))) == 3.5);
    // fabs(-0.0) == +0.0: value compares equal to 0, and the sign bit
    // of the result must be clear.
    REQUIRE(eval(ieee_fabs(fc(-0.0))) == 0.0);
    REQUIRE_FALSE(eval_bool(ieee_signbit(ieee_fabs(fc(-0.0)))));
  }

  SECTION("copysign takes the sign from the sign bit of the source")
  {
    // The negative-zero cases are the ones a `< 0` implementation gets
    // wrong: -0.0 is not < 0, yet copysign must treat it as negative.
    REQUIRE(eval(ieee_copysign(fc(1.0), fc(-0.0))) == -1.0);
    REQUIRE(eval_bool(ieee_signbit(ieee_copysign(fc(1.0), fc(-0.0)))));
    REQUIRE(eval(ieee_copysign(fc(1.0), fc(0.0))) == 1.0);
    REQUIRE_FALSE(eval_bool(ieee_signbit(ieee_copysign(fc(1.0), fc(0.0)))));
    REQUIRE(eval(ieee_copysign(fc(1.0), fc(-5.0))) == -1.0);
    REQUIRE(eval(ieee_copysign(fc(-1.0), fc(5.0))) == 1.0);
    REQUIRE(eval(ieee_copysign(fc(2.0), fc(-3.0))) == -2.0);
    // Magnitude's own sign is irrelevant; only its absolute value is used.
    REQUIRE(eval(ieee_copysign(fc(-2.0), fc(3.0))) == 2.0);
  }
}

TEST_CASE(
  "ieee_float_valuet to_double / to_float round-trip",
  "[core][util][ieee_float]")
{
  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };
  auto from_float = [](float f) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_float(f);
    return v;
  };

  SECTION("to_double is a bit-exact reinterpretation")
  {
    REQUIRE(from_double(0.0).to_double() == 0.0);
    REQUIRE(from_double(1.0).to_double() == 1.0);
    REQUIRE(from_double(-2.5).to_double() == -2.5);
    REQUIRE(from_double(3.14159).to_double() == 3.14159);
    REQUIRE(
      from_double(std::numeric_limits<double>::infinity()).to_double() ==
      std::numeric_limits<double>::infinity());
    REQUIRE(
      from_double(std::numeric_limits<double>::max()).to_double() ==
      std::numeric_limits<double>::max());
  }

  SECTION("to_float is a bit-exact reinterpretation")
  {
    REQUIRE(from_float(0.0f).to_float() == 0.0f);
    REQUIRE(from_float(1.0f).to_float() == 1.0f);
    REQUIRE(from_float(-2.5f).to_float() == -2.5f);
    REQUIRE(
      from_float(std::numeric_limits<float>::infinity()).to_float() ==
      std::numeric_limits<float>::infinity());
  }
}

TEST_CASE(
  "ieee_float_valuet to_integer truncates towards zero",
  "[core][util][ieee_float]")
{
  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };

  // to_integer always rounds towards zero (truncation), independent of any
  // rounding mode -- this is the caveat that justifies it living on
  // ieee_float_valuet rather than ieee_floatt.
  SECTION("positive values truncate down")
  {
    REQUIRE(from_double(0.0).to_integer() == 0);
    REQUIRE(from_double(0.9).to_integer() == 0);
    REQUIRE(from_double(1.0).to_integer() == 1);
    REQUIRE(from_double(3.9).to_integer() == 3);
    REQUIRE(from_double(1e10).to_integer() == 10000000000);
  }

  SECTION("negative values truncate towards zero, not down")
  {
    REQUIRE(from_double(-0.0).to_integer() == 0);
    REQUIRE(from_double(-0.9).to_integer() == 0);
    REQUIRE(from_double(-1.0).to_integer() == -1);
    // truncation towards zero gives -3, not -4 (which round-to-minus-infinity
    // would give)
    REQUIRE(from_double(-3.9).to_integer() == -3);
    REQUIRE(from_double(-1e10).to_integer() == -10000000000);
  }

  SECTION("NaN and infinities map to zero")
  {
    const auto dp = ieee_float_spect::double_precision();
    REQUIRE(ieee_float_valuet::NaN(dp).to_integer() == 0);
    REQUIRE(ieee_float_valuet::plus_infinity(dp).to_integer() == 0);
    REQUIRE(ieee_float_valuet::minus_infinity(dp).to_integer() == 0);
  }
}
