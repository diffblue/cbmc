/*******************************************************************\

Module: Unit tests for float utils and approximation

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/catch.hpp>

// for debug output in case of failure
#include <iostream>
#include <limits>
#include <random>

#include <solvers/floatbv/float_approximation.h>
#include <solvers/floatbv/float_utils.h>
#include <solvers/sat/satcheck.h>

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

static bool eq(const ieee_floatt &a, const ieee_floatt &b)
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
  ieee_floatt &i1,
  ieee_floatt &i2)
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
  const ieee_floatt &i1,
  const ieee_floatt &i2)
{
  const bvt b1 = float_utils.build_constant(i1);
  const bvt b2 = float_utils.build_constant(i2);

  const auto op = i % 3;

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
  const ieee_floatt &i1,
  const ieee_floatt &i2,
  const ieee_floatt &i3,
  const ieee_floatt &fres,
  const float &f1,
  const float &f2,
  const float &f3)
{
  const unsigned op = i % 3;
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
  ieee_floatt i1, i2, i3;
  float f1, f2, f3;

  std::random_device rd;
  std::mt19937 gen(rd());
  distt dist(0, std::numeric_limits<unsigned>::max());

  for(unsigned i = 0; i < 200; i++)
  {
    satcheckt satcheck;
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

        const ieee_floatt fres = float_utils.get(res);

        if(!eq(fres, i3))
          print(i, i1, i2, i3, fres, f1, f2, f3);

        REQUIRE(eq(fres, i3));
      }
    }
  }
}

SCENARIO("float_approximation", "[core][solvers][floatbv][float_approximation]")
{
  ieee_floatt i1, i2, i3;
  float f1, f2, f3;

  std::random_device rd;
  std::mt19937 gen(rd());
  distt dist(0, std::numeric_limits<unsigned>::max());

  for(unsigned i = 0; i < 200; i++)
  {
    satcheckt satcheck;
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

        const ieee_floatt fres = float_utils.get(res);

        if(!eq(fres, i3))
          print(i, i1, i2, i3, fres, f1, f2, f3);

        REQUIRE(eq(fres, i3));
      }
    }
  }
}
