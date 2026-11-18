/*******************************************************************\

Module: Unit tests for round_to_integral

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <solvers/floatbv/float_bv.h>
#include <solvers/floatbv/float_utils.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <vector>

static const std::vector<ieee_floatt::rounding_modet> rounding_modes{
  ieee_floatt::ROUND_TO_EVEN,
  ieee_floatt::ROUND_TO_MINUS_INF,
  ieee_floatt::ROUND_TO_PLUS_INF,
  ieee_floatt::ROUND_TO_ZERO,
  ieee_floatt::ROUND_TO_AWAY};

/// The exact result of rounding \p value to an integral value in \p mode.
static ieee_float_valuet
reference(const ieee_float_valuet &value, ieee_floatt::rounding_modet mode)
{
  if(value.is_NaN() || value.is_infinity() || value.is_zero())
    return value;

  mp_integer fraction, exponent;
  value.extract_base2(fraction, exponent);
  if(exponent >= 0)
    return value;

  const mp_integer divisor = power(2, -exponent);
  mp_integer integer = fraction / divisor;
  const mp_integer remainder = fraction % divisor;
  const mp_integer twice_remainder = 2 * remainder;
  const bool sign = value.get_sign();
  bool up = false;
  switch(mode)
  {
  case ieee_floatt::ROUND_TO_EVEN:
    up = twice_remainder > divisor ||
         (twice_remainder == divisor && integer % 2 == 1);
    break;
  case ieee_floatt::ROUND_TO_AWAY:
    up = twice_remainder >= divisor;
    break;
  case ieee_floatt::ROUND_TO_PLUS_INF:
    up = !sign;
    break;
  case ieee_floatt::ROUND_TO_MINUS_INF:
    up = sign;
    break;
  case ieee_floatt::ROUND_TO_ZERO:
    break;
  case ieee_floatt::UNKNOWN:
  case ieee_floatt::NONDETERMINISTIC:
    UNREACHABLE;
  }
  if(up)
    ++integer;

  // the integral value is exact, or not representable: then infinity
  ieee_floatt result{value.spec, mode};
  result.from_integer(sign ? -integer : integer);
  if(result.is_zero() && sign)
    result.negate();
  return result;
}

static bool same(const ieee_float_valuet &a, const ieee_float_valuet &b)
{
  return (a.is_NaN() && b.is_NaN()) || a.pack() == b.pack();
}

TEST_CASE(
  "round_to_integral agrees with the exact result in small formats",
  "[core][solvers][floatbv]")
{
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};

  // formats with 1- and 2-bit exponents, in which 0.5 or 1 are subnormal,
  // and formats in which 2^f is not a finite value
  for(const auto &e_f : std::vector<std::pair<std::size_t, std::size_t>>{
        {1, 2}, {1, 3}, {2, 1}, {2, 2}, {2, 3}, {3, 2}, {3, 4}, {4, 3}, {5, 2}})
  {
    const ieee_float_spect spec{e_f.second, e_f.first};
    const std::size_t width = spec.width();

    for(const auto mode : rounding_modes)
    {
      for(mp_integer bits = 0; bits < power(2, width); ++bits)
      {
        ieee_floatt value{spec, mode};
        value.unpack(bits);
        const ieee_float_valuet expected = reference(value, mode);

        // the constant folding of the simplifier
        const ieee_float_valuet folded = value.round_to_integral();

        // the propositional encoding
        satcheckt satcheck{null_message_handler};
        float_utilst float_utils{satcheck, spec.to_type()};
        float_utils.rounding_mode_bits.set(mode);
        const bvt result_bv =
          float_utils.round_to_integral(float_utils.build_constant(value));
        REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
        const ieee_float_valuet encoded = float_utils.get(result_bv);

        // the bit-vector encoding used by the SMT back-ends
        const exprt result_expr = simplify_expr(
          float_bvt{}.round_to_integral(
            value.to_expr(), from_integer(mode, signedbv_typet{32}), spec),
          ns);
        REQUIRE(result_expr.is_constant());
        const ieee_float_valuet rewritten{to_constant_expr(result_expr)};

        INFO(
          "e=" << spec.e << " f=" << spec.f << " mode=" << mode
               << " input=" << integer2binary(bits, width)
               << " expected=" << integer2binary(expected.pack(), width));
        CHECK(same(folded, expected));
        CHECK(same(encoded, expected));
        CHECK(same(rewritten, expected));
      }
    }
  }
}
