/*******************************************************************\

Module: Unit tests for util/ieee_float

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/ieee_float.h>

#include <testing-utils/use_catch.h>

#include <cfloat>
#include <cmath>
#include <cstring>
#include <limits>
#include <random>

#define PINF (std::numeric_limits<float>::infinity())
#define NINF (-std::numeric_limits<float>::infinity())
#ifndef NZERO
#  define NZERO (-0.0f)
#endif
#define PZERO (0.0f)

#ifndef NAN
#  define NAN (std::numeric_limits<float>::quiet_NaN())
#endif

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

namespace
{
// Fixed seed so that any failure is reproducible from the logs.
std::mt19937 seeded_generator()
{
  return std::mt19937(0x1234abcd);
}

float random_float(std::mt19937 &gen)
{
  std::uniform_int_distribution<unsigned> dist(0, 19);
  unsigned r = dist(gen);

  switch(r)
  {
  case 0:
    return PINF;
    break;
  case 1:
    return NINF;
    break;
  case 2:
    return NAN;
    break;
  case 3:
    return PZERO;
    break;
  case 4:
    return NZERO;
    break;
  default:
    std::uniform_int_distribution<unsigned> rand_dist(
      0, std::numeric_limits<unsigned>::max());
    unsigned bits = rand_dist(gen);
    bits = (bits << 16) ^ rand_dist(gen);
    float f;
    static_assert(sizeof(f) == sizeof(bits), "float must be 32 bits");
    std::memcpy(&f, &bits, sizeof(f));
    return f;
  }
}

bool eq(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.is_NaN() && b.is_NaN())
    return true;
  if(a.is_infinity() && b.is_infinity() && a.get_sign() == b.get_sign())
    return true;
  return a == b;
}

typedef enum
{
  PLUS = 0,
  MINUS = 1,
  MULT = 2,
  DIV = 3
} binopt;
typedef enum
{
  EQ = 0,
  NEQ = 1,
  LT = 2,
  LE = 3,
  GT = 4,
  GE = 5
} binrel;
} // namespace

TEST_CASE("IEEE float arithmetic operations", "[core][util][ieee_float]")
{
  std::mt19937 gen = seeded_generator();

  for(unsigned i = 0; i < 1000; i++)
  {
    ieee_float_valuet i1, i2, i3;

    float f1 = random_float(gen);
    float f2 = random_float(gen);
    i1.from_float(f1);
    i2.from_float(f2);
    ieee_floatt res{i1, ieee_floatt::ROUND_TO_EVEN};
    ieee_floatt i2r{i2, ieee_floatt::ROUND_TO_EVEN};
    float f3 = f1;

    int op = i % 4;

    switch(op)
    {
    case PLUS:
      f3 += f2;
      res += i2r;
      break;

    case MINUS:
      f3 -= f2;
      res -= i2r;
      break;

    case MULT:
      f3 *= f2;
      res *= i2r;
      break;

    case DIV:
      f3 /= f2;
      res /= i2r;
      break;

    default:
      REQUIRE(false);
    }

    i3.from_float(f3);
    REQUIRE(eq(res, ieee_floatt{i3, ieee_floatt::ROUND_TO_EVEN}));
  }
}

TEST_CASE("IEEE float comparison operations", "[core][util][ieee_float]")
{
  std::mt19937 gen = seeded_generator();

  for(unsigned i = 0; i < 1000; i++)
  {
    ieee_float_valuet i1, i2;
    bool ires = false, fres = false;

    float f1 = random_float(gen);
    float f2 = random_float(gen);
    i1.from_float(f1);
    i2.from_float(f2);

    int op = i % 6;

    switch(op)
    {
    case EQ:
      ires = i1.ieee_equal(i2);
      fres = (f1 == f2);
      break;
    case NEQ:
      ires = i1.ieee_not_equal(i2);
      fres = (f1 != f2);
      break;
    case LT:
      ires = (i1 < i2);
      fres = (f1 < f2);
      break;
    case LE:
      ires = (i1 <= i2);
      fres = (f1 <= f2);
      break;
    case GT:
      ires = (i1 > i2);
      fres = (f1 > f2);
      break;
    case GE:
      ires = (i1 >= i2);
      fres = (f1 >= f2);
      break;
    default:
      REQUIRE(false);
    }

    REQUIRE(ires == fres);
  }
}

TEST_CASE("IEEE float conversion", "[core][util][ieee_float]")
{
  std::mt19937 gen = seeded_generator();

  for(unsigned i = 0; i < 1000; i++)
  {
    float a_f = random_float(gen);

    ieee_float_valuet t;
    t.from_float(a_f);

    REQUIRE(t.is_float());
    float b_f = t.to_float();

    std::uint32_t a_i, b_i;
    static_assert(
      sizeof(float) == sizeof(std::uint32_t), "float must be 32 bits");
    std::memcpy(&a_i, &a_f, sizeof(a_f));
    std::memcpy(&b_i, &b_f, sizeof(b_f));

    bool same = (a_i == b_i) || ((a_f != a_f) && (b_f != b_f));
    REQUIRE(same);
  }
}

#ifndef _WIN32
TEST_CASE("IEEE float nextafter", "[core][util][ieee_float]")
{
  std::mt19937 gen = seeded_generator();

  for(unsigned i = 0; i < 100; i++)
  {
    float f1 = random_float(gen);
    float f2 = nextafterf(f1, PINF);
    float f3 = nextafterf(f1, NINF);

    ieee_float_valuet i1, i2, i3;

    i1.from_float(f1);
    i2 = i1;
    i2.increment(false);
    i3 = i1;
    i3.decrement(false);

    bool match1 = (f1 == i1.to_float()) || (f1 != f1 && i1.is_NaN());
    bool match2 = (f2 == i2.to_float()) || (f2 != f2 && i2.is_NaN());
    bool match3 = (f3 == i3.to_float()) || (f3 != f3 && i3.is_NaN());

    REQUIRE(match1);
    REQUIRE(match2);
    REQUIRE(match3);
  }
}
#endif

TEST_CASE("IEEE float min/max", "[core][util][ieee_float]")
{
  float f = 0;
  ieee_float_valuet t;
  t.from_float(f);

  t.make_fltmax();
  REQUIRE(t.to_float() == FLT_MAX);

  t.make_fltmin();
  REQUIRE(t.to_float() == FLT_MIN);
}

TEST_CASE("IEEE float build/extract", "[core][util][ieee_float]")
{
  std::mt19937 gen = seeded_generator();

  for(unsigned i = 0; i < 100; i++)
  {
    float f = random_float(gen);
    ieee_floatt t{
      ieee_float_spect::single_precision(), ieee_floatt::ROUND_TO_EVEN};
    t.from_float(f);

    mp_integer old_frac, old_exp;
    t.extract_base2(old_frac, old_exp);
    mp_integer frac_bak = old_frac, exp_bak = old_exp;
    t.build(old_frac, old_exp);
    t.extract_base2(old_frac, old_exp);

    REQUIRE(frac_bak == old_frac);
    REQUIRE(exp_bak == old_exp);
  }
}
