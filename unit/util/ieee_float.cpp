/*******************************************************************\

Module: Unit tests for util/ieee_float

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/ieee_float.h>

#include <testing-utils/use_catch.h>

#include <limits>
#include <random>

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

/// An exact binary rational number fraction * 2^exponent
struct exact_valuet
{
  mp_integer fraction, exponent;

  explicit exact_valuet(const ieee_float_valuet &v)
  {
    v.extract_base2(fraction, exponent);
  }

  exact_valuet(mp_integer _fraction, mp_integer _exponent)
    : fraction(std::move(_fraction)), exponent(std::move(_exponent))
  {
  }
};

/// \return -1, 0, 1 if a is less than, equal to, greater than b
static int compare(const exact_valuet &a, const exact_valuet &b)
{
  const mp_integer min_exponent = std::min(a.exponent, b.exponent);
  const mp_integer x =
    a.fraction *
    power(2, numeric_cast_v<std::size_t>(a.exponent - min_exponent));
  const mp_integer y =
    b.fraction *
    power(2, numeric_cast_v<std::size_t>(b.exponent - min_exponent));
  return x < y ? -1 : (x == y ? 0 : 1);
}

static exact_valuet square(const exact_valuet &a)
{
  return {a.fraction * a.fraction, 2 * a.exponent};
}

static exact_valuet midpoint(const exact_valuet &a, const exact_valuet &b)
{
  const mp_integer min_exponent = std::min(a.exponent, b.exponent);
  return {
    a.fraction *
        power(2, numeric_cast_v<std::size_t>(a.exponent - min_exponent)) +
      b.fraction *
        power(2, numeric_cast_v<std::size_t>(b.exponent - min_exponent)),
    min_exponent - 1};
}

/// Checks that \p result is the square root of the positive, finite \p x,
/// correctly rounded according to \p rm, using exact arithmetic.
static bool is_correctly_rounded_sqrt(
  const ieee_float_valuet &x,
  const ieee_float_valuet &result,
  ieee_floatt::rounding_modet rm)
{
  if(result.is_NaN() || result.is_infinity() || result.is_zero())
    return false;
  if(result.get_sign() || !result.is_normal())
    return false;

  ieee_float_valuet next = result;
  next.increment();
  ieee_float_valuet previous = result;
  previous.decrement();

  const exact_valuet x_value{x};
  const exact_valuet r{result};
  // next is +Inf iff result is the largest number, whose square exceeds x
  const bool below_next =
    next.is_infinity() || compare(x_value, square(exact_valuet{next})) < 0;
  const bool above_previous =
    compare(square(exact_valuet{previous}), x_value) < 0;

  switch(rm)
  {
  case ieee_floatt::ROUND_TO_MINUS_INF:
  case ieee_floatt::ROUND_TO_ZERO:
    return compare(square(r), x_value) <= 0 && below_next;
  case ieee_floatt::ROUND_TO_PLUS_INF:
    return above_previous && compare(x_value, square(r)) <= 0;
  case ieee_floatt::ROUND_TO_EVEN:
  case ieee_floatt::ROUND_TO_AWAY:
    // there are no ties
    return compare(square(midpoint(exact_valuet{previous}, r)), x_value) < 0 &&
           (next.is_infinity() ||
            compare(x_value, square(midpoint(r, exact_valuet{next}))) < 0);
  case ieee_floatt::NONDETERMINISTIC:
  case ieee_floatt::UNKNOWN:
    break;
  }
  return false;
}

TEST_CASE("ieee_floatt::sqrt", "[core][util][ieee_float]")
{
  const ieee_floatt::rounding_modet rounding_modes[] = {
    ieee_floatt::ROUND_TO_EVEN,
    ieee_floatt::ROUND_TO_MINUS_INF,
    ieee_floatt::ROUND_TO_PLUS_INF,
    ieee_floatt::ROUND_TO_ZERO,
    ieee_floatt::ROUND_TO_AWAY};

  SECTION("special values")
  {
    const auto dp = ieee_float_spect::double_precision();
    for(const auto rm : rounding_modes)
    {
      const auto NaN = ieee_float_valuet::NaN(dp);
      REQUIRE(ieee_floatt{NaN, rm}.sqrt().is_NaN());
      const auto plus_inf = ieee_float_valuet::plus_infinity(dp);
      REQUIRE(ieee_floatt{plus_inf, rm}.sqrt() == plus_inf);
      const auto minus_inf = ieee_float_valuet::minus_infinity(dp);
      REQUIRE(ieee_floatt{minus_inf, rm}.sqrt().is_NaN());
      ieee_float_valuet zero{dp};
      zero.make_zero();
      REQUIRE(ieee_floatt{zero, rm}.sqrt().is_zero());
      REQUIRE(!ieee_floatt{zero, rm}.sqrt().get_sign());
      zero.negate();
      REQUIRE(ieee_floatt{zero, rm}.sqrt().is_zero());
      REQUIRE(ieee_floatt{zero, rm}.sqrt().get_sign());
      ieee_float_valuet minus_one{dp};
      minus_one.from_double(-1.0);
      REQUIRE(ieee_floatt{minus_one, rm}.sqrt().is_NaN());
    }
  }

  SECTION("exhaustively in a small format")
  {
    // 1 sign bit, 4 exponent bits, 6 fraction bits
    const ieee_float_spect spec{6, 4};
    for(mp_integer bits = 1; bits < power(2, spec.f + spec.e); ++bits)
    {
      ieee_float_valuet x{spec};
      x.unpack(bits);
      if(x.is_NaN() || x.is_infinity())
        continue;
      for(const auto rm : rounding_modes)
      {
        INFO("bits: " << bits << ", rounding mode: " << rm);
        REQUIRE(is_correctly_rounded_sqrt(x, ieee_floatt{x, rm}.sqrt(), rm));
      }
    }
  }

  SECTION("random values in single, double, and quadruple precision")
  {
    std::mt19937_64 gen{42};
    for(const auto &spec :
        {ieee_float_spect::single_precision(),
         ieee_float_spect::double_precision(),
         ieee_float_spect::quadruple_precision()})
    {
      for(std::size_t i = 0; i < 200; ++i)
      {
        // random positive finite values, including subnormal ones
        mp_integer bits = 0;
        for(std::size_t b = 0; b < spec.f + spec.e; b += 32)
          bits = bits * power(2, 32) + (gen() & 0xffffffffu);
        bits %= power(2, spec.f + spec.e);
        ieee_float_valuet x{spec};
        x.unpack(bits);
        if(x.is_NaN() || x.is_infinity() || x.is_zero())
          continue;
        for(const auto rm : rounding_modes)
        {
          INFO("bits: " << bits << ", rounding mode: " << rm);
          REQUIRE(is_correctly_rounded_sqrt(x, ieee_floatt{x, rm}.sqrt(), rm));
        }
      }
    }
  }
}
