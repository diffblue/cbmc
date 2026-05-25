// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "Overflow expression construction as binary_overflow_exprt",
  "[core][util][expr]")
{
  std::string kind;
  std::function<bool(const exprt &)> can_cast;
  using rowt = std::pair<std::string, std::function<bool(const exprt &)>>;
  std::tie(kind, can_cast) = GENERATE(
    rowt{"+", can_cast_expr<plus_overflow_exprt>},
    rowt{"*", can_cast_expr<mult_overflow_exprt>},
    rowt{"-", can_cast_expr<minus_overflow_exprt>},
    rowt{"shl", can_cast_expr<shl_overflow_exprt>});
  SECTION("For " + kind + " overflow.")
  {
    const symbol_exprt left{"left", unsignedbv_typet{8}};
    const symbol_exprt right{"right", unsignedbv_typet{8}};
    const binary_overflow_exprt overflow{left, kind, right};
    SECTION("Expression can be downcast.")
    {
      REQUIRE(can_cast(overflow));
    }
    SECTION("Operand getters")
    {
      REQUIRE(overflow.lhs() == left);
      REQUIRE(overflow.rhs() == right);
    }
  }
}

TEMPLATE_TEST_CASE(
  "Overflow expression sub classes",
  "[core][util][expr]",
  plus_overflow_exprt,
  mult_overflow_exprt,
  minus_overflow_exprt,
  shl_overflow_exprt)
{
  SECTION("Construction")
  {
    const symbol_exprt left{"left", unsignedbv_typet{8}};
    const symbol_exprt right{"right", unsignedbv_typet{8}};
    const TestType sub_class{left, right};
    SECTION("Upcast")
    {
      const auto binary_overflow_expr =
        expr_try_dynamic_cast<binary_overflow_exprt>(sub_class);
      REQUIRE(binary_overflow_expr);
      SECTION("Downcast")
      {
        REQUIRE(expr_try_dynamic_cast<TestType>(*binary_overflow_expr));
      }
    }
    SECTION("Operand getters")
    {
      REQUIRE(sub_class.lhs() == left);
      REQUIRE(sub_class.rhs() == right);
    }
  }
}

TEST_CASE("onehot expression lowering", "[core][util][expr]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);
  satcheckt satcheck{message_handler};
  boolbvt boolbv{empty_namespace, satcheck, message_handler};
  unsignedbv_typet u8{8};

  GIVEN("A bit-vector that is one-hot")
  {
    boolbv << onehot_exprt{from_integer(64, u8)}.lower();

    THEN("the lowering of onehot is true")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot")
  {
    boolbv << onehot_exprt{from_integer(5, u8)}.lower();

    THEN("the lowering of onehot is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot")
  {
    boolbv << onehot_exprt{from_integer(0, u8)}.lower();

    THEN("the lowering of onehot is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is one-hot 0")
  {
    boolbv << onehot0_exprt{from_integer(0xfe, u8)}.lower();

    THEN("the lowering of onehot0 is true")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot 0")
  {
    boolbv << onehot0_exprt{from_integer(0x7e, u8)}.lower();

    THEN("the lowering of onehot0 is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot 0")
  {
    boolbv << onehot0_exprt{from_integer(0xff, u8)}.lower();

    THEN("the lowering of onehot0 is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}

TEMPLATE_TEST_CASE(
  "reduction expression sub classes",
  "[core][util][expr]",
  reduction_and_exprt,
  reduction_or_exprt,
  reduction_nand_exprt,
  reduction_nor_exprt,
  reduction_xor_exprt,
  reduction_xnor_exprt)
{
  const symbol_exprt sym{"x", unsignedbv_typet{4}};
  const TestType red{sym};

  SECTION("can_cast_expr true for matching expression")
  {
    REQUIRE(can_cast_expr<TestType>(red));
  }

  SECTION("can_cast_expr false for non-matching expression")
  {
    const plus_exprt binary{sym, sym};
    REQUIRE_FALSE(can_cast_expr<TestType>(binary));
  }

  SECTION("expr_try_dynamic_cast round-trip")
  {
    const exprt &base = red;
    auto *p = expr_try_dynamic_cast<TestType>(base);
    REQUIRE(p != nullptr);
    REQUIRE(p->op() == sym);
  }
}
