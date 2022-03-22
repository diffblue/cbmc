// Author: Diffblue Ltd.

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>

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
