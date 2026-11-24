/*******************************************************************\

Module: Unit tests for bv_utilst

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Unit tests for bv_utilst

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/flattening/bv_utils.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

SCENARIO("1-bit signed less-than", "[core][solvers][flattening][bv_utils]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("Two 1-bit signed bitvector symbols")
  {
    satcheckt satcheck(message_handler);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    boolbvt boolbv(ns, satcheck, message_handler);

    signedbv_typet s1(1);
    auto x = symbol_exprt("x", s1);
    auto y = symbol_exprt("y", s1);

    THEN("-1 < 0 is satisfiable")
    {
      // x = -1, y = 0, x < y
      boolbv << equal_exprt(x, from_integer(-1, s1));
      boolbv << equal_exprt(y, from_integer(0, s1));
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }

    THEN("0 < -1 is unsatisfiable")
    {
      boolbv << equal_exprt(x, from_integer(0, s1));
      boolbv << equal_exprt(y, from_integer(-1, s1));
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }

    THEN("-1 <= -1 is satisfiable")
    {
      boolbv << equal_exprt(x, from_integer(-1, s1));
      boolbv << equal_exprt(y, from_integer(-1, s1));
      boolbv << less_than_or_equal_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }

    THEN("-1 < -1 is unsatisfiable")
    {
      boolbv << equal_exprt(x, from_integer(-1, s1));
      boolbv << equal_exprt(y, from_integer(-1, s1));
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }

    THEN("x < y is satisfiable for symbolic 1-bit signed values")
    {
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }

    THEN("x <= y is satisfiable for symbolic 1-bit signed values")
    {
      boolbv << less_than_or_equal_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }
}

SCENARIO(
  "unsigned_divider folds constant operands",
  "[core][solvers][flattening][bv_utils]")
{
  GIVEN("a bv_utilst over a SAT back-end")
  {
    satcheckt satcheck(null_message_handler);
    bv_utilst bv_utils(satcheck);
    const std::size_t width = 32;

    WHEN("dividing two constants 100 / 7")
    {
      bvt res, rem;
      bv_utils.divider(
        bv_utilst::build_constant(100, width),
        bv_utilst::build_constant(7, width),
        res,
        rem,
        bv_utilst::representationt::UNSIGNED);

      THEN("the result is constant (no fresh variables) and correct")
      {
        REQUIRE(bv_utilst::is_constant(res));
        REQUIRE(bv_utilst::is_constant(rem));
        REQUIRE(res == bv_utilst::build_constant(14, width));
        REQUIRE(rem == bv_utilst::build_constant(2, width));
      }
    }

    WHEN("dividing a constant by a non-constant divisor")
    {
      bvt res, rem;
      bv_utils.divider(
        bv_utilst::build_constant(100, width),
        satcheck.new_variables(width),
        res,
        rem,
        bv_utilst::representationt::UNSIGNED);

      THEN("the fast path is bypassed and the result is non-constant")
      {
        // The is_constant(op0) && is_constant(op1) guard must remain
        // a conjunction: a non-constant divisor must not be folded.
        REQUIRE_FALSE(bv_utilst::is_constant(res));
        REQUIRE_FALSE(bv_utilst::is_constant(rem));
      }
    }

    WHEN("exact division 100 / 5")
    {
      bvt res, rem;
      bv_utils.divider(
        bv_utilst::build_constant(100, width),
        bv_utilst::build_constant(5, width),
        res,
        rem,
        bv_utilst::representationt::UNSIGNED);

      THEN("the result is constant with quotient 20 and rem 0")
      {
        REQUIRE(bv_utilst::is_constant(res));
        REQUIRE(bv_utilst::is_constant(rem));
        REQUIRE(res == bv_utilst::build_constant(20, width));
        REQUIRE(rem == bv_utilst::build_constant(0, width));
      }
    }

    WHEN("dividing by one")
    {
      bvt res, rem;
      bv_utils.divider(
        bv_utilst::build_constant(100, width),
        bv_utilst::build_constant(1, width),
        res,
        rem,
        bv_utilst::representationt::UNSIGNED);

      THEN("res equals the numerator and rem is zero")
      {
        REQUIRE(bv_utilst::is_constant(res));
        REQUIRE(bv_utilst::is_constant(rem));
        REQUIRE(res == bv_utilst::build_constant(100, width));
        REQUIRE(rem == bv_utilst::build_constant(0, width));
      }
    }

    WHEN("dividing a constant by a constant zero")
    {
      bvt res, rem;
      bv_utils.divider(
        bv_utilst::build_constant(100, width),
        bv_utilst::build_constant(0, width),
        res,
        rem,
        bv_utilst::representationt::UNSIGNED);

      THEN("the fall-through (nondeterministic) encoding is used")
      {
        // division by zero must not be folded; it keeps fresh variables
        REQUIRE_FALSE(bv_utilst::is_constant(res));
        REQUIRE_FALSE(bv_utilst::is_constant(rem));
      }
    }
  }
}

SCENARIO(
  "multipliers compute the product modulo 2^width",
  "[core][solvers][flattening][bv_utils]")
{
  const std::size_t width = 4;
  const mp_integer modulus = power(2, width);

  for(const auto rep :
      {bv_utilst::representationt::SIGNED,
       bv_utilst::representationt::UNSIGNED})
  {
    for(mp_integer a = 0; a < modulus; ++a)
    {
      for(mp_integer b = 0; b < modulus; ++b)
      {
        satcheckt satcheck(null_message_handler);
        bv_utilst bv_utils(satcheck);
        const bvt a_constant = bv_utilst::build_constant(a, width);
        const bvt b_constant = bv_utilst::build_constant(b, width);
        const bvt x = satcheck.new_variables(width);
        const bvt y = satcheck.new_variables(width);
        satcheck.l_set_to_true(bv_utils.equal(x, a_constant));
        satcheck.l_set_to_true(bv_utils.equal(y, b_constant));

        // non-constant operands, and a constant one in either position, which
        // the multiplier may negate
        const std::vector<bvt> products{
          bv_utils.multiplier(x, y, rep),
          bv_utils.multiplier(x, b_constant, rep),
          bv_utils.multiplier(a_constant, y, rep)};

        REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);

        const bvt expected =
          bv_utilst::build_constant((a * b) % modulus, width);
        for(const auto &product : products)
        {
          REQUIRE(product.size() == width);
          for(std::size_t i = 0; i < width; ++i)
            REQUIRE(satcheck.l_get(product[i]) == satcheck.l_get(expected[i]));
        }
      }
    }
  }
}
