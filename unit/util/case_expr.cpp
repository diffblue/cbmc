/*******************************************************************\

Module: Unit tests for case_exprt

Author: Unit test

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE("case_exprt construction and access", "[core][util][case_expr]")
{
  const signedbv_typet int_type(32);
  const symbol_exprt select_value("x", int_type);

  SECTION("Basic construction")
  {
    case_exprt case_expr(select_value, int_type);

    REQUIRE(case_expr.id() == ID_case);
    REQUIRE(case_expr.select_value() == select_value);
    REQUIRE(case_expr.number_of_cases() == 0);
  }

  SECTION("Adding cases")
  {
    case_exprt case_expr(select_value, int_type);

    const constant_exprt case1_value = from_integer(1, int_type);
    const constant_exprt result1_value = from_integer(10, int_type);

    const constant_exprt case2_value = from_integer(2, int_type);
    const constant_exprt result2_value = from_integer(20, int_type);

    case_expr.add_case(case1_value, result1_value);
    REQUIRE(case_expr.number_of_cases() == 1);
    REQUIRE(case_expr.case_value(0) == case1_value);
    REQUIRE(case_expr.result_value(0) == result1_value);

    case_expr.add_case(case2_value, result2_value);
    REQUIRE(case_expr.number_of_cases() == 2);
    REQUIRE(case_expr.case_value(1) == case2_value);
    REQUIRE(case_expr.result_value(1) == result2_value);

    // Verify operands structure: 1 select + 2*2 case/result pairs = 5
    REQUIRE(case_expr.operands().size() == 5);
    // Verify odd number of operands
    REQUIRE(case_expr.operands().size() % 2 == 1);
  }

  SECTION("to_case_expr conversion")
  {
    case_exprt case_expr(select_value, int_type);
    const constant_exprt case_value = from_integer(1, int_type);
    const constant_exprt result_value = from_integer(10, int_type);
    case_expr.add_case(case_value, result_value);

    exprt &base = case_expr;
    case_exprt &converted = to_case_expr(base);

    REQUIRE(&converted == &case_expr);
    REQUIRE(converted.number_of_cases() == 1);
    REQUIRE(converted.case_value(0) == case_value);
  }

  SECTION("can_cast_expr")
  {
    case_exprt case_expr(select_value, int_type);
    exprt &base = case_expr;

    REQUIRE(can_cast_expr<case_exprt>(base));
    REQUIRE_FALSE(can_cast_expr<if_exprt>(base));
  }

  SECTION("Construction with operands")
  {
    const constant_exprt case_value = from_integer(1, int_type);
    const constant_exprt result_value = from_integer(10, int_type);

    case_exprt::operandst ops;
    ops.push_back(select_value);
    ops.push_back(case_value);
    ops.push_back(result_value);

    case_exprt case_expr(std::move(ops), int_type);

    REQUIRE(case_expr.id() == ID_case);
    REQUIRE(case_expr.number_of_cases() == 1);
    REQUIRE(case_expr.select_value() == select_value);
    REQUIRE(case_expr.case_value(0) == case_value);
    REQUIRE(case_expr.result_value(0) == result_value);
  }
}
