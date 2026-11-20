/*******************************************************************\

Module: Unit tests for float utils and approximation

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

// for debug output in case of failure
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/floatbv/float_approximation.h>
#include <solvers/floatbv/float_bv.h>
#include <solvers/floatbv/float_utils.h>
#include <solvers/sat/satcheck.h>

#include <iostream>
#include <limits>
#include <random>

typedef std::uniform_int_distribution<unsigned> distt;

static float random_float(distt &dist, std::mt19937 &gen)
{
  union
  {
    float f;
    unsigned int i;
  } u;

  u.i = dist(gen);
  u.i = (u.i << 16) ^ dist(gen);

  return u.f;
}

static bool eq(const ieee_float_valuet &a, const ieee_float_valuet &b)
{
  return (a.is_NaN() && b.is_NaN()) ||
         (a.is_infinity() && b.is_infinity() && a.get_sign() == b.get_sign()) ||
         a == b;
}

#if 0
static std::string to_str(const bvt &bv)
{
  std::string result;
  for(unsigned i=0; i<bv.size(); i++)
  {
    char ch;
    if(bv[i]==const_literal(true))
      ch='1';
    else if(bv[i]==const_literal(false))
      ch='0';
    else
      ch='?';
    result=ch+result;
  }
  return result;
}
#endif

typedef enum { PLUS=0, MINUS=1, MULT=2, DIV=3 } binopt;
const char *binopsyms[]={ " + ", " - ", " * ", " / " };

static float set_values(
  distt &dist,
  std::mt19937 &gen,
  float_utilst &float_utils,
  float &f1,
  float &f2,
  ieee_float_valuet &i1,
  ieee_float_valuet &i2)
{
  f1 = random_float(dist, gen);
  f2 = random_float(dist, gen);
  i1.from_float(f1);
  i2.from_float(f2);
  float_utils.spec = i1.spec;

  return f1;
}

static bvt compute(
  unsigned i,
  float_utilst &float_utils,
  const float &f2,
  float &f3,
  const ieee_float_valuet &i1,
  const ieee_float_valuet &i2)
{
  const bvt b1 = float_utils.build_constant(i1);
  const bvt b2 = float_utils.build_constant(i2);

  const auto op = i % 4;

  switch(op)
  {
  case PLUS:
    f3 += f2;
    return float_utils.add(b1, b2);

  case MINUS:
    f3 -= f2;
    return float_utils.sub(b1, b2);

  case MULT:
    f3 *= f2;
    return float_utils.mul(b1, b2);

  case DIV:
    f3 /= f2;
    return float_utils.div(b1, b2);
  }

  return bvt();
}

static void print(
  unsigned i,
  const ieee_float_valuet &i1,
  const ieee_float_valuet &i2,
  const ieee_float_valuet &i3,
  const ieee_float_valuet &fres,
  const float &f1,
  const float &f2,
  const float &f3)
{
  const unsigned op = i % 4;
  const char *opsym = binopsyms[op];

  std::cout << i1 << opsym << i2 << " != " << fres << '\n';
  std::cout << f1 << opsym << f2 << " == " << f3 << '\n';
  std::cout << integer2binary(i1.get_exponent(), i1.spec.e) << " "
            << integer2binary(i1.get_fraction(), i1.spec.f + 1) << opsym
            << integer2binary(i2.get_exponent(), i1.spec.e) << " "
            << integer2binary(i2.get_fraction(), i1.spec.f + 1) << " != "
            << integer2binary(fres.get_exponent(), i1.spec.e) << " "
            << integer2binary(fres.get_fraction(), i1.spec.f + 1) << '\n';
  std::cout << integer2binary(i1.get_exponent(), i1.spec.e) << " "
            << integer2binary(i1.get_fraction(), i1.spec.f + 1) << opsym
            << integer2binary(i2.get_exponent(), i1.spec.e) << " "
            << integer2binary(i2.get_fraction(), i1.spec.f + 1) << " == "
            << integer2binary(i3.get_exponent(), i1.spec.e) << " "
            << integer2binary(i3.get_fraction(), i1.spec.f + 1) << '\n';
}

SCENARIO("float_utils", "[core][solvers][floatbv][float_utils]")
{
  ieee_float_valuet i1, i2, i3;
  float f1, f2, f3;

  std::random_device rd;
  std::mt19937 gen(rd());
  distt dist(0, std::numeric_limits<unsigned>::max());

  for(unsigned i = 0; i < 200; i++)
  {
    satcheckt satcheck(null_message_handler);
    float_utilst float_utils(satcheck);

    GIVEN("Two random floating point numbers")
    {
      f3 = set_values(dist, gen, float_utils, f1, f2, i1, i2);
      bvt res = compute(i, float_utils, f2, f3, i1, i2);

      THEN("Machine execution yields the same result as symbolic computation")
      {
        i3.from_float(f3);

        const satcheckt::resultt result = satcheck.prop_solve();
        REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

        const ieee_float_valuet fres = float_utils.get(res);

        if(!eq(fres, i3))
          print(i, i1, i2, i3, fres, f1, f2, f3);

        REQUIRE(eq(fres, i3));
      }
    }
  }
}

SCENARIO("float_approximation", "[core][solvers][floatbv][float_approximation]")
{
  ieee_float_valuet i1, i2, i3;
  float f1, f2, f3;

  std::random_device rd;
  std::mt19937 gen(rd());
  distt dist(0, std::numeric_limits<unsigned>::max());

  for(unsigned i = 0; i < 200; i++)
  {
    satcheckt satcheck(null_message_handler);
    float_approximationt float_utils(satcheck);

    GIVEN("Two random floating point numbers")
    {
      f3 = set_values(dist, gen, float_utils, f1, f2, i1, i2);
      bvt res = compute(i, float_utils, f2, f3, i1, i2);

      THEN("Machine execution yields the same result as symbolic computation")
      {
        i3.from_float(f3);

        const satcheckt::resultt result = satcheck.prop_solve();
        REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

        const ieee_float_valuet fres = float_utils.get(res);

        if(!eq(fres, i3))
          print(i, i1, i2, i3, fres, f1, f2, f3);

        REQUIRE(eq(fres, i3));
      }
    }
  }
}

static ieee_float_valuet
round_to_integral(ieee_float_valuet op, ieee_floatt::rounding_modet rm)
{
  satcheckt satcheck(null_message_handler);
  float_utilst float_utils(satcheck);
  float_utils.rounding_mode_bits.set(rm);
  float_utils.spec = op.spec;

  // add constraint
  auto op_bv = float_utils.build_constant(op);
  bvt result_bv = float_utils.round_to_integral(op_bv);

  // solve
  const auto result = satcheck.prop_solve();
  REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

  return float_utils.get(result_bv);
}

SCENARIO(
  "float_utils_round_to_integral",
  "[core][solvers][floatbv][float_utils][round_to_integral]")
{
  const auto dp = ieee_float_spect::double_precision();

  const auto NaN = ieee_float_valuet::NaN(dp);
  const auto plus_inf = ieee_float_valuet::plus_infinity(dp);
  const auto minus_inf = ieee_float_valuet::minus_infinity(dp);
  const auto dmax = std::numeric_limits<double>::max();

  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };

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

SCENARIO("float_utils_fma", "[core][solvers][floatbv][float_utils]")
{
  // Test fused multiply-add: round(a * b + c) with single rounding.
  // The key property: the product a*b is computed exactly before adding c.

  satcheckt satcheck(null_message_handler);
  float_utilst float_utils(satcheck);
  float_utils.spec = ieee_float_spect::single_precision();
  auto rm = bv_utilst(satcheck).build_constant(ieee_floatt::ROUND_TO_EVEN, 32);
  float_utils.set_rounding_mode(rm);

  auto from_float = [](float f)
  {
    ieee_float_valuet v{ieee_float_spect::single_precision()};
    v.from_float(f);
    return v;
  };

  auto check_fma = [&](float a, float b, float c, float expected)
  {
    const bvt ba = float_utils.build_constant(from_float(a));
    const bvt bb = float_utils.build_constant(from_float(b));
    const bvt bc = float_utils.build_constant(from_float(c));
    const bvt result = float_utils.fma(ba, bb, bc);

    const satcheckt::resultt sat_result = satcheck.prop_solve();
    REQUIRE(sat_result == satcheckt::resultt::P_SATISFIABLE);

    const ieee_float_valuet fres = float_utils.get(result);
    const ieee_float_valuet fexp = from_float(expected);

    if(!eq(fres, fexp))
    {
      std::cout << "fma(" << a << ", " << b << ", " << c << ") = " << fres
                << " (expected " << fexp << ")\n";
    }
    REQUIRE(eq(fres, fexp));
  };

  GIVEN("Basic FMA operations")
  {
    THEN("Simple cases are correct")
    {
      check_fma(2.0f, 3.0f, 4.0f, 10.0f);
      check_fma(-3.0f, 2.0f, 10.0f, 4.0f);
      check_fma(0.0f, 100.0f, 5.0f, 5.0f);
      check_fma(1.0f, 1.0f, -1.0f, 0.0f);
    }
  }

  GIVEN("FMA differs from mul+add due to single rounding")
  {
    THEN("FMA preserves precision lost by separate mul+add")
    {
      // 0x1.fffffep+23 * 0x1.000002p+0 + 1.0:
      // mul rounds product, losing low bit -> 0x1p+24
      // FMA keeps exact product -> 0x1.000002p+24
      check_fma(0x1.fffffep+23f, 0x1.000002p+0f, 1.0f, 0x1.000002p+24f);
    }
  }

  GIVEN("FMA for remainder computation")
  {
    THEN("fma(-n, y, x) is more precise than x - n*y")
    {
      // x = 0x1.d55556p+0, y = 0x1.555556p-2, n = 5
      // x - 5*y with separate ops: 0x1.55555p-3 (two roundings)
      // fma(-5, y, x): 0x1.555554p-3 (single rounding, more precise)
      check_fma(-5.0f, 0x1.555556p-2f, 0x1.d55556p+0f, 0x1.555554p-3f);
    }
  }
}

static ieee_float_valuet
float_utils_sqrt(const ieee_float_valuet &op, ieee_floatt::rounding_modet rm)
{
  satcheckt satcheck(null_message_handler);
  float_utilst float_utils(satcheck);
  float_utils.rounding_mode_bits.set(rm);
  float_utils.spec = op.spec;

  bvt result_bv = float_utils.sqrt(float_utils.build_constant(op));

  const auto result = satcheck.prop_solve();
  REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

  return float_utils.get(result_bv);
}

static ieee_float_valuet
float_bv_sqrt(const ieee_float_valuet &op, ieee_floatt::rounding_modet rm)
{
  const symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  const float_bvt float_bv;
  const exprt result = float_bv.sqrt(
    op.to_expr(), from_integer(rm, unsignedbv_typet{32}), op.spec);

  // The expression is a DAG with lots of sharing, which the propositional
  // back-end, unlike the simplifier, converts in linear time.
  satcheckt satcheck(null_message_handler);
  boolbvt solver{ns, satcheck, null_message_handler};
  const symbol_exprt result_symbol{"result", result.type()};
  solver.set_to_true(equal_exprt{result_symbol, result});
  REQUIRE(solver() == decision_proceduret::resultt::D_SATISFIABLE);
  const exprt value = solver.get(result_symbol);
  REQUIRE(value.is_constant());
  // float_bv uses bit-vector types
  return ieee_float_valuet{
    constant_exprt{to_constant_expr(value).get_value(), op.spec.to_type()}};
}

SCENARIO("float_utils_sqrt", "[core][solvers][floatbv][float_utils][sqrt]")
{
  const ieee_floatt::rounding_modet rounding_modes[] = {
    ieee_floatt::ROUND_TO_EVEN,
    ieee_floatt::ROUND_TO_MINUS_INF,
    ieee_floatt::ROUND_TO_PLUS_INF,
    ieee_floatt::ROUND_TO_ZERO,
    ieee_floatt::ROUND_TO_AWAY};

  GIVEN("all values of a small format")
  {
    // 1 sign bit, 4 exponent bits, 6 fraction bits; includes the special
    // values and negative numbers
    const ieee_float_spect spec{6, 4};
    for(mp_integer bits = 0; bits < power(2, spec.width()); ++bits)
    {
      ieee_float_valuet x{spec};
      x.unpack(bits);
      for(const auto rm : rounding_modes)
      {
        INFO("bits: " << bits << ", rounding mode: " << rm);
        const auto expected = ieee_floatt{x, rm}.sqrt();
        const auto result = float_utils_sqrt(x, rm);
        REQUIRE(eq(result, expected));
        const auto result_bv = float_bv_sqrt(x, rm);
        REQUIRE(eq(result_bv, expected));
        // the sign of zero matters, the sign of NaN does not
        if(!expected.is_NaN())
        {
          REQUIRE(result.get_sign() == expected.get_sign());
          REQUIRE(result_bv.get_sign() == expected.get_sign());
        }
      }
    }
  }

  GIVEN("random single-precision values")
  {
    std::random_device rd;
    std::mt19937 gen(rd());
    distt dist(0, std::numeric_limits<unsigned>::max());

    for(std::size_t i = 0; i < 100; ++i)
    {
      ieee_float_valuet x;
      x.from_float(random_float(dist, gen));
      for(const auto rm : rounding_modes)
      {
        INFO("x: " << x << ", rounding mode: " << rm);
        REQUIRE(eq(float_utils_sqrt(x, rm), ieee_floatt{x, rm}.sqrt()));
      }
    }
  }
}

/// Prove that sqrt(y) * sqrt(y) <= y * (1 + k * epsilon) for all non-negative
/// finite y, with all operations rounded according to \p rm.
/// \return true iff the property holds
static bool square_of_sqrt_is_bounded(
  const ieee_float_spect &spec,
  ieee_floatt::rounding_modet rm,
  unsigned k)
{
  satcheckt satcheck(null_message_handler);
  float_utilst float_utils(satcheck);
  float_utils.rounding_mode_bits.set(rm);
  float_utils.spec = spec;

  const bvt y = satcheck.new_variables(spec.width());
  satcheck.l_set_to_false(float_utils.is_NaN(y));
  satcheck.l_set_to_false(float_utils.is_infinity(y));
  satcheck.l_set_to_false(float_utils.sign_bit(y));

  // 1 + k * epsilon
  ieee_floatt bound{spec, ieee_floatt::ROUND_TO_EVEN};
  bound.build(power(2, spec.f) + k, -mp_integer{spec.f});

  const bvt root = float_utils.sqrt(y);
  const bvt square = float_utils.mul(root, root);
  const bvt limit = float_utils.mul(y, float_utils.build_constant(bound));
  satcheck.l_set_to_false(
    float_utils.relation(square, float_utilst::relt::LE, limit));

  return satcheck.prop_solve() == satcheckt::resultt::P_UNSATISFIABLE;
}

SCENARIO(
  "float_utils_sqrt_symbolic",
  "[core][solvers][floatbv][float_utils][sqrt]")
{
  // The tightest bounds on sqrt(y) * sqrt(y) in multiples of epsilon. Proving
  // these for all values is fast for 16-bit formats, but not for single
  // precision.
  const std::pair<ieee_floatt::rounding_modet, unsigned> bounds[] = {
    {ieee_floatt::ROUND_TO_EVEN, 1},
    {ieee_floatt::ROUND_TO_MINUS_INF, 0},
    {ieee_floatt::ROUND_TO_PLUS_INF, 2},
    {ieee_floatt::ROUND_TO_ZERO, 0}};

  // bfloat16 (8 exponent bits, 7 fraction bits) and IEEE binary16
  for(const auto &spec :
      {ieee_float_spect{7, 8}, ieee_float_spect::half_precision()})
  {
    for(const auto &[rm, k] : bounds)
    {
      INFO("f: " << spec.f << ", rounding mode: " << rm);
      REQUIRE(square_of_sqrt_is_bounded(spec, rm, k));
      if(k > 0)
        REQUIRE(!square_of_sqrt_is_bounded(spec, rm, k - 1));
    }
  }
}
