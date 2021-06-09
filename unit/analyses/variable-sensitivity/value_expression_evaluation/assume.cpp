/*******************************************************************\

 Module: Unit tests for abstract_environmentt::assume

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

exprt binary_expression(
  dstringt const &exprId,
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto op1_sym = symbol_exprt("op1", op1->type());
  auto op2_sym = symbol_exprt("op2", op2->type());
  environment.assign(op1_sym, op1, ns);
  environment.assign(op2_sym, op2, ns);

  return binary_relation_exprt(op1_sym, exprId, op2_sym);
}

static void ASSUME_TRUE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);
static void ASSUME_FALSE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);
static void
ASSUME_NIL(abstract_environmentt &env, const exprt &expr, const namespacet &ns);

std::vector<std::string>
split(std::string const &s, std::string const &delimiter);
std::vector<exprt> numbersToExprs(std::vector<std::string> const &numbers);

class assume_testert
{
public:
  void operator()(bool is_true, std::vector<std::string> const &tests)
  {
    for(auto test : tests)
    {
      if(is_test(test, "=="))
        test_fn(ID_equal, is_true, test, "==");
      else if(is_test(test, "!="))
        test_fn(ID_notequal, is_true, test, "!=");
      else if(is_test(test, "<="))
        test_fn(ID_le, is_true, test, "<=");
      else if(is_test(test, ">="))
        test_fn(ID_ge, is_true, test, ">=");
      else if(is_test(test, "<"))
        test_fn(ID_lt, is_true, test, "<");
      else if(is_test(test, ">"))
        test_fn(ID_gt, is_true, test, ">");
      else
        FAIL("Unknown test: " + test);
    }
  }

  bool is_test(std::string const &test, std::string const &delimiter)
  {
    return test.find(delimiter) != std::string::npos;
  }

  void test_fn(
    dstringt const &exprId,
    bool is_true,
    std::string const &test,
    std::string const &delimiter)
  {
    WHEN(test)
    {
      auto operands = split(test, delimiter);
      REQUIRE(operands.size() == 2);

      auto op1 = build_op(operands[0]);
      auto op2 = build_op(operands[1]);

      auto test_expr = binary_expression(exprId, op1, op2, environment, ns);

      if(is_true)
        ASSUME_TRUE(environment, test_expr, ns);
      else
        ASSUME_FALSE(environment, test_expr, ns);
    }
  }

  assume_testert(abstract_environmentt &env, namespacet &n)
    : environment(env), ns(n)
  {
  }

private:
  abstract_object_pointert build_op(std::string const &optext)
  {
    auto stripped = std::string{};
    for(auto i : optext)
      if(i != ' ')
        stripped.push_back(i);

    switch(stripped[0])
    {
    case '{':
      return build_value_set(stripped);
    case '[':
      return build_interval(stripped);
    default:
      return build_constant(stripped);
    }
  }

  abstract_object_pointert build_value_set(std::string const &optext)
  {
    auto numbers = split(optext.substr(1, optext.size() - 2), ",");
    auto exprs = numbersToExprs(numbers);
    REQUIRE(exprs.size() > 0);

    return make_value_set(exprs, environment, ns);
  }
  abstract_object_pointert build_interval(std::string const &optext)
  {
    auto numbers = split(optext.substr(1, optext.size() - 2), ",");
    auto exprs = numbersToExprs(numbers);
    REQUIRE(exprs.size() == 2);

    return make_interval(exprs[0], exprs[1], environment, ns);
  }
  abstract_object_pointert build_constant(std::string const &optext)
  {
    auto expr = numbersToExprs({optext})[0];

    return make_constant(expr, environment, ns);
  }

  const typet type = signedbv_typet(32);

  abstract_environmentt &environment;
  namespacet &ns;
};

SCENARIO(
  "assume value expressions",
  "[core][analyses][variable-sensitivity][constant_abstract_value][value_set_"
  "abstract_object][interval_abstract_value][assume]")
{
  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  assume_testert assumeTester(environment, ns);

  GIVEN("true or false")
  {
    WHEN("true")
    {
      ASSUME_TRUE(environment, true_exprt(), ns);
    }
    WHEN("false")
    {
      ASSUME_FALSE(environment, false_exprt(), ns);
    }
    WHEN("!true")
    {
      ASSUME_FALSE(environment, not_exprt(true_exprt()), ns);
    }
    WHEN("!false")
    {
      ASSUME_TRUE(environment, not_exprt(false_exprt()), ns);
    }

    auto type = signedbv_typet(32);
    auto val1 = from_integer(1, type);
    auto val2 = from_integer(2, type);
    auto val3 = from_integer(3, type);
    auto val4 = from_integer(4, type);
    auto val5 = from_integer(5, type);
    auto constant1 = make_constant(val1, environment, ns);
    auto constant3 = make_constant(val3, environment, ns);
    auto interval12 = make_interval(val1, val2, environment, ns);

    WHEN("1 == 1")
    {
      auto is_equal =
        binary_expression(ID_equal, constant1, constant1, environment, ns);
      ASSUME_TRUE(environment, is_equal, ns);
    }
    WHEN("!(1 == 1)")
    {
      auto is_equal =
        binary_expression(ID_equal, constant1, constant1, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_equal), ns);
    }
    WHEN("[1,2] == 1")
    {
      auto is_equal =
        binary_expression(ID_equal, interval12, constant1, environment, ns);
      ASSUME_TRUE(environment, is_equal, ns);
    }
    WHEN("!([1,2] == 1)")
    {
      auto is_equal =
        binary_expression(ID_equal, interval12, constant1, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_equal), ns);
    }
    WHEN("1 != 3")
    {
      auto is_not_equal =
        binary_expression(ID_notequal, constant1, constant3, environment, ns);
      ASSUME_TRUE(environment, is_not_equal, ns);
    }
    WHEN("!(1 != 3)")
    {
      auto is_not_equal =
        binary_expression(ID_notequal, constant1, constant3, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_not_equal), ns);
    }
    WHEN("[1,2] != 3")
    {
      auto is_not_equal =
        binary_expression(ID_notequal, interval12, constant3, environment, ns);
      ASSUME_TRUE(environment, is_not_equal, ns);
    }
    WHEN("!([1,2] != 3)")
    {
      auto is_not_equal =
        binary_expression(ID_notequal, interval12, constant3, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_not_equal), ns);
    }
    WHEN("1 <= 3")
    {
      auto is_le =
        binary_expression(ID_le, constant1, constant3, environment, ns);
      ASSUME_TRUE(environment, is_le, ns);
    }
    WHEN("!(1 <= 3)")
    {
      auto is_le =
        binary_expression(ID_le, constant1, constant3, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_le), ns);
    }
    WHEN("[1,2] <= 3")
    {
      auto is_le =
        binary_expression(ID_le, interval12, constant3, environment, ns);
      ASSUME_TRUE(environment, is_le, ns);
    }
    WHEN("!([1,2] <= 3)")
    {
      auto is_le =
        binary_expression(ID_le, interval12, constant3, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_le), ns);
    }
    WHEN("3 > 1")
    {
      auto is_le =
        binary_expression(ID_gt, constant3, constant1, environment, ns);
      ASSUME_TRUE(environment, is_le, ns);
    }
    WHEN("!(3 > 1)")
    {
      auto is_le =
        binary_expression(ID_gt, constant3, constant1, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_le), ns);
    }
    WHEN("3 > [1,2]")
    {
      auto is_le =
        binary_expression(ID_gt, constant3, interval12, environment, ns);
      ASSUME_TRUE(environment, is_le, ns);
    }
    WHEN("!(3 > [1,2])")
    {
      auto is_le =
        binary_expression(ID_gt, constant3, interval12, environment, ns);
      ASSUME_FALSE(environment, not_exprt(is_le), ns);
    }
  }

  GIVEN("expected equality")
  {
    assumeTester(
      true,
      {"2 == 2",
       "[1, 1] == 1",
       "[1, 1] == [1, 1]",
       "[1, 1] == { 1 }",
       "[1, 2] == 1",
       "[1, 2] == [1, 1]",
       "[1, 2] == { 1 }",
       "[1, 2] == 2",
       "[1, 2] == [2, 2]",
       "[1, 2] == [1, 2]",
       "[1, 2] == {1, 2}",
       "[1, 3] == 2",
       "[1, 3] == [2, 2]",
       "[1, 3] == { 2 }",
       "{ 1 } == 1",
       "{ 1, 2 } == 1",
       "{ 1, 2 } == [ 1, 1 ]",
       "{ 1, 2 } == [ 1, 2 ]",
       "{ 1, 2 } == [ 1, 3 ]",
       "{ 1, 2 } == [ 2, 5 ]",
       "{ 1, 2 } == { 1 }",
       "{ 1, 2 } == { 2 }",
       "{ 1, 2 } == { 1, 2 }",
       "{ 1, 2 } == { 1, 3 }",
       "{ 1, 2 } == { 2, 5 }"});
  }
  GIVEN("expected not equality")
  {
    assumeTester(
      false,
      {"1 == 2",
       "[2, 3] == 1",
       "[2, 3] == [1, 1]",
       "{ 2, 3 } == 1",
       "{ 1, 2, 3 } == [ 6, 10 ]",
       "{ 2, 3 } == { 4, 5 }"});
  }

  GIVEN("expected inequality")
  {
    assumeTester(
      true,
      {"1 != 2",
       "[2, 3] != 1",
       "[2, 3] != [1, 1]",
       "{ 2, 3 } != 1",
       "{ 1, 2, 3 } != [ 6, 10 ]",
       "{ 2, 3 } != { 4, 5 }"});
  }
  GIVEN("expected not inequality")
  {
    assumeTester(
      false,
      {"2 != 2",
       "[1, 1] != 1",
       "[1, 1] != [1, 1]",
       "[1, 1] != { 1 }",
       "[1, 2] != 1",
       "[1, 2] != [1, 1]",
       "[1, 2] != { 1 }",
       "[1, 2] != 2",
       "[1, 2] != [2, 2]",
       "[1, 2] != [1, 2]",
       "[1, 2] != {1, 2}",
       "[1, 3] != 2",
       "[1, 3] != [2, 2]",
       "[1, 3] != { 2 }",
       "{ 1 } != 1",
       "{ 1, 2 } != 1",
       "{ 1, 2 } != [ 1, 1 ]",
       "{ 1, 2 } != [ 1, 2 ]",
       "{ 1, 2 } != [ 1, 3 ]",
       "{ 1, 2 } != [ 2, 5 ]",
       "{ 1, 2 } != { 1 }",
       "{ 1, 2 } != { 2 }",
       "{ 1, 2 } != { 1, 2 }",
       "{ 1, 2 } != { 1, 3 }",
       "{ 1, 2 } != { 2, 5 }"});
  }
  GIVEN("expected less than or equal to")
  {
    assumeTester(
      true,
      {
        "1 <= 1",
        "1 <= 2",
        "1 <= [1, 2]",
        "2 <= [1, 2]",
        "1 <= [0, 2]",
        "1 <= { 0, 1 }",
        "1 <= { 1 }",
        "[1, 2] <= 1",
        "[1, 2] <= 2",
        "[1, 2] <= 5",
        "[1, 5] <= [1, 2]",
        "[1, 5] <= [1, 5]",
        "[1, 5] <= [1, 7]",
        "[1, 5] <= [0, 7]",
        "[1, 5] <= [0, 3]",
        "[1, 5] <= { 1, 2 }",
        "[1, 5] <= { 1, 5 }",
        "[1, 5] <= { 1, 7 }",
        "[1, 5] <= { 0, 7 }",
        "[1, 5] <= { 0, 3 }",
        "[1, 5] <= { 0, 1 }",
        "{ 1, 2 } <= 1",
        "{ 1, 2 } <= 2",
        "{ 1, 2 } <= 5",
        "{ 1, 5 } <= [1, 2]",
        "{ 1, 5 } <= [1, 5]",
        "{ 1, 5 } <= [1, 7]",
        "{ 1, 5 } <= [0, 7]",
        "{ 1, 5 } <= [0, 3]",
        "{ 1, 5 } <= { 1, 2 }",
        "{ 1, 5 } <= { 1, 5 }",
        "{ 1, 5 } <= { 1, 7 }",
        "{ 1, 5 } <= { 0, 7 }",
        "{ 1, 5 } <= { 0, 3 }",
        "{ 1, 5 } <= { 0, 1 }",
      });
  }
  GIVEN("expected not less than or equal to")
  {
    assumeTester(
      false,
      {"2 <= 1",
       "[2, 3] <= 1",
       "[2, 3] <= [0, 1]",
       "[2, 3] <= { 0, 1 }",
       "{ 2, 3, 4 } <= 1",
       "{ 2, 4 } <= [0, 1]",
       "{ 2, 4 } <= { 0, 1 }"});
  }
  GIVEN("expected less than")
  {
    assumeTester(
      true,
      {"1 < 2",
       "1 < [1, 2]",
       "1 < [0, 2]",
       "1 < { 1, 2 }",
       "1 < { 0, 2 }",
       "[1, 2] < 2",
       "[1, 2] < 5",
       "[1, 5] < [1, 2]",
       "[1, 5] < [1, 5]",
       "[1, 5] < [1, 7]",
       "[1, 5] < [0, 7]",
       "[1, 5] < [0, 3]",
       "[1, 5] < { 1, 2 }",
       "[1, 5] < { 1, 5 }",
       "[1, 5] < { 1, 7 }",
       "[1, 5] < { 0, 7 }",
       "[1, 5] < { 0, 3 }",
       "{ 1, 2 } < 2",
       "{ 1, 2 } < 5",
       "{ 1, 5 } < [1, 2]",
       "{ 1, 5 } < [1, 5]",
       "{ 1, 5 } < [1, 7]",
       "{ 1, 5 } < [0, 7]",
       "{ 1, 5 } < [0, 3]",
       "{ 1, 5 } < { 1, 2 }",
       "{ 1, 5 } < { 1, 5 }",
       "{ 1, 5 } < { 1, 7 }",
       "{ 1, 5 } < { 0, 7 }",
       "{ 1, 5 } < { 0, 3 }"});
  }
  GIVEN("expected not less than")
  {
    assumeTester(
      false,
      {"2 < 1",
       "2 < 2",
       "[2, 3] < 1",
       "[2, 3] < 2",
       "[2, 3] < [0, 1]",
       "[2, 3] < [0, 2]",
       "[2, 3] < { 0, 1 }",
       "[2, 3] < { 0, 2 }",
       "{ 2, 3, 4 } < 1",
       "{ 2, 3, 4 } < 2",
       "{ 2, 4 } < [0, 1]",
       "{ 2, 4 } < [0, 2]",
       "{ 2, 4 } < { 0, 1 }",
       "{ 2, 4 } < { 0, 2 }"});
  }
  GIVEN("expected greater than or equal to")
  {
    assumeTester(
      true,
      {
        "1 >= 1",
        "1 >= 0",
        "1 >= [1, 2]",
        "2 >= [1, 2]",
        "1 >= [0, 2]",
        "1 >= { 0, 1 }",
        "1 >= { 1 }",
        "[1, 2] >= 0",
        "[1, 2] >= 1",
        "[1, 2] >= 2",
        "[1, 5] >= [1, 2]",
        "[1, 5] >= [1, 5]",
        "[1, 5] >= [1, 7]",
        "[1, 5] >= [0, 7]",
        "[1, 5] >= [0, 3]",
        "[1, 5] >= { 1, 2 }",
        "[1, 5] >= { 1, 5 }",
        "[1, 5] >= { 1, 7 }",
        "[1, 5] >= { 0, 7 }",
        "[1, 5] >= { 0, 3 }",
        "[1, 5] >= { 0, 1 }",
        "{ 1, 2 } >= 0",
        "{ 1, 2 } >= 1",
        "{ 1, 2 } >= 2",
        "{ 1, 5 } >= [1, 2]",
        "{ 1, 5 } >= [1, 5]",
        "{ 1, 5 } >= [1, 7]",
        "{ 1, 5 } >= [0, 7]",
        "{ 1, 5 } >= [0, 3]",
        "{ 1, 5 } >= { 1, 2 }",
        "{ 1, 5 } >= { 1, 5 }",
        "{ 1, 5 } >= { 1, 7 }",
        "{ 1, 5 } >= { 0, 7 }",
        "{ 1, 5 } >= { 0, 3 }",
        "{ 1, 5 } >= { 0, 1 }",
      });
  }
  GIVEN("expected not greater than or equal")
  {
    assumeTester(
      false,
      {"1 >= 2",
       "1 >= [2, 3]",
       "[0, 1] >= 2",
       "[0, 1] >= [2 ,3]",
       "[0, 1] >= { 2, 3 }",
       "{ 0, 1, 2 } >= 3",
       "{ 0, 1 } >= [2, 3]",
       "{ 0, 1 } >= { 2, 3 }"});
  }
  GIVEN("expected greater than")
  {
    assumeTester(
      true,
      {
        "1 > 0",
        "2 > [1, 2]",
        "1 > [0, 2]",
        "1 > { 0, 1 }",
        "1 > { 0 }",
        "[1, 2] > 0",
        "[1, 2] > 1",
        "[1, 5] > [1, 2]",
        "[1, 5] > [1, 5]",
        "[1, 5] > [1, 7]",
        "[1, 5] > [0, 7]",
        "[1, 5] > [0, 3]",
        "[1, 5] > { 1, 2 }",
        "[1, 5] > { 1, 5 }",
        "[1, 5] > { 1, 7 }",
        "[1, 5] > { 0, 7 }",
        "[1, 5] > { 0, 3 }",
        "[1, 5] > { 0, 1 }",
        "{ 1, 2 } > 0",
        "{ 1, 2 } > 1",
        "{ 1, 5 } > [1, 2]",
        "{ 1, 5 } > [1, 5]",
        "{ 1, 5 } > [1, 7]",
        "{ 1, 5 } > [0, 7]",
        "{ 1, 5 } > [0, 3]",
        "{ 1, 5 } > { 1, 2 }",
        "{ 1, 5 } > { 1, 5 }",
        "{ 1, 5 } > { 1, 7 }",
        "{ 1, 5 } > { 0, 7 }",
        "{ 1, 5 } > { 0, 3 }",
        "{ 1, 5 } > { 0, 1 }",
      });
  }
  GIVEN("expected not greater than")
  {
    assumeTester(
      false,
      {"1 > 1",
       "1 > 2",
       "1 > [1, 3]",
       "1 > [2, 3]",
       "[0, 1] > 1",
       "[0, 1] > 2",
       "[0, 1] > [1 ,3]",
       "[0, 1] > [2 ,3]",
       "[0, 1] > { 1, 3 }",
       "[0, 1] > { 2, 3 }",
       "{ 0, 1, 2 } > 2",
       "{ 0, 1, 2 } > 3",
       "{ 0, 1 } > [1, 3]",
       "{ 0, 1 } > [2, 3]",
       "{ 0, 1 } > { 1, 3 }",
       "{ 0, 1 } > { 2, 3 }"});
  }
  GIVEN("and expressions")
  {
    auto type = signedbv_typet(32);
    auto val1 = from_integer(1, type);
    auto val2 = from_integer(2, type);
    auto val3 = from_integer(3, type);
    auto val4 = from_integer(4, type);
    auto val5 = from_integer(5, type);

    auto v12 = make_value_set({val1, val2}, environment, ns);
    auto v23 = make_value_set({val2, val3}, environment, ns);
    auto v34 = make_value_set({val3, val4}, environment, ns);
    auto v45 = make_value_set({val4, val5}, environment, ns);

    auto c1_sym = symbol_exprt("c1", v12->type());
    auto c2_sym = symbol_exprt("c2", v23->type());
    auto c3_sym = symbol_exprt("c3", v23->type());
    auto c4_sym = symbol_exprt("c4", v23->type());
    environment.assign(c1_sym, v12, ns);
    environment.assign(c2_sym, v23, ns);
    environment.assign(c3_sym, v34, ns);
    environment.assign(c4_sym, v45, ns);

    WHEN("{ 1, 2 } == { 2, 3 } && { 3, 4 } == { 4, 5 }")
    {
      auto lhs_expr = equal_exprt(c1_sym, c2_sym);
      auto rhs_expr = equal_exprt(c3_sym, c4_sym);

      auto and_expr = and_exprt(lhs_expr, rhs_expr);

      ASSUME_TRUE(environment, and_expr, ns);
    }
    WHEN("{ 1, 2 } == { 2, 3 } && { 3, 4 } == { 4, 5 } && { 1, 2 } != { 3, 4 }")
    {
      auto expr0 = equal_exprt(c1_sym, c2_sym);
      auto expr1 = equal_exprt(c3_sym, c4_sym);
      auto expr2 = notequal_exprt(c1_sym, c4_sym);

      auto and_expr = and_exprt(expr0, expr1, expr2);

      ASSUME_TRUE(environment, and_expr, ns);
    }
    WHEN(
      "{ 1, 2 } == { 2, 3 } && { 3, 4 } == { 4, 5 } && !({ 1, 2 } == { 3, 4 })")
    {
      auto expr0 = equal_exprt(c1_sym, c2_sym);
      auto expr1 = equal_exprt(c3_sym, c4_sym);
      auto expr2 = not_exprt(equal_exprt(c1_sym, c4_sym));

      auto and_expr = and_exprt(expr0, expr1, expr2);

      ASSUME_TRUE(environment, and_expr, ns);
    }
    WHEN("unknown == { 2, 3 } && { 3, 4 } == { 4, 5 }")
    {
      auto unknown = symbol_exprt("unknown", v23->type());
      auto lhs_expr = equal_exprt(unknown, c2_sym);
      auto rhs_expr = equal_exprt(c3_sym, c4_sym);

      auto and_expr = and_exprt(lhs_expr, rhs_expr);

      ASSUME_TRUE(environment, and_expr, ns);
    }
    WHEN("{ 3, 4 } == { 4, 5 } && unknown == { 2, 3 }")
    {
      auto unknown = symbol_exprt("unknown", v23->type());
      auto lhs_expr = equal_exprt(c3_sym, c4_sym);
      auto rhs_expr = equal_exprt(unknown, c2_sym);

      auto and_expr = and_exprt(lhs_expr, rhs_expr);

      ASSUME_TRUE(environment, and_expr, ns);
    }
    WHEN("unknown == { 2, 3 } && mystery == { 1, 2 }")
    {
      auto unknown = symbol_exprt("unknown", v23->type());
      auto lhs_expr = equal_exprt(unknown, c2_sym);
      auto mystery = symbol_exprt("mystery", v23->type());
      auto rhs_expr = equal_exprt(mystery, c1_sym);

      auto and_expr = and_exprt(lhs_expr, rhs_expr);

      ASSUME_TRUE(environment, and_expr, ns);
    }
    WHEN("unknown == { 2, 3 } && { 3, 4 } == { 1, 2 }")
    {
      auto unknown = symbol_exprt("unknown", v23->type());
      auto lhs_expr = equal_exprt(unknown, c2_sym);
      auto rhs_expr = equal_exprt(c3_sym, c1_sym);

      auto and_expr = and_exprt(lhs_expr, rhs_expr);

      ASSUME_FALSE(environment, and_expr, ns);
    }
    WHEN("{ 1, 2 } == { 4, 5 } && { 3, 4 } == { 1, 2 }")
    {
      auto expr0 = equal_exprt(c1_sym, c4_sym);
      auto expr1 = equal_exprt(c3_sym, c1_sym);

      auto and_expr = and_exprt(expr0, expr1);

      ASSUME_FALSE(environment, and_expr, ns);
    }
  }
  GIVEN("or expressions")
  {
    auto type = signedbv_typet(32);
    auto val1 = from_integer(1, type);
    auto val2 = from_integer(2, type);
    auto val3 = from_integer(3, type);
    auto val4 = from_integer(4, type);
    auto val5 = from_integer(5, type);

    auto v12 = make_value_set({val1, val2}, environment, ns);
    auto v23 = make_value_set({val2, val3}, environment, ns);
    auto v34 = make_value_set({val3, val4}, environment, ns);
    auto v45 = make_value_set({val4, val5}, environment, ns);

    auto c1_sym = symbol_exprt("c1", v12->type());
    auto c2_sym = symbol_exprt("c2", v23->type());
    auto c3_sym = symbol_exprt("c3", v23->type());
    auto c4_sym = symbol_exprt("c4", v23->type());
    environment.assign(c1_sym, v12, ns);
    environment.assign(c2_sym, v23, ns);
    environment.assign(c3_sym, v34, ns);
    environment.assign(c4_sym, v45, ns);

    WHEN("{ 1, 2 } == { 2, 3 } || { 3, 4 } == { 4, 5 }")
    {
      auto lhs_expr = equal_exprt(c1_sym, c2_sym);
      auto rhs_expr = equal_exprt(c3_sym, c4_sym);

      auto or_expr = or_exprt(lhs_expr, rhs_expr);

      ASSUME_TRUE(environment, or_expr, ns);
    }
    WHEN("{ 1, 2 } == { 2, 3 } || { 3, 4 } == { 4, 5 } || { 1, 2 } != { 3, 4 }")
    {
      auto expr0 = equal_exprt(c1_sym, c2_sym);
      auto expr1 = equal_exprt(c3_sym, c4_sym);
      auto expr2 = notequal_exprt(c1_sym, c4_sym);

      auto or_expr = or_exprt(expr0, expr1, expr2);

      ASSUME_TRUE(environment, or_expr, ns);
    }
    WHEN("{ 1, 2 } == { 2, 3 } && { 3, 4 } != { 4, 5 }")
    {
      auto expr0 = equal_exprt(c1_sym, c2_sym);
      auto expr1 = notequal_exprt(c3_sym, c4_sym);

      auto or_expr = or_exprt(expr0, expr1);

      ASSUME_TRUE(environment, or_expr, ns);
    }
    WHEN("unknown == { 2, 3 } || { 3, 4 } == { 4, 5 }")
    {
      auto unknown = symbol_exprt("unknown", v23->type());
      auto lhs_expr = equal_exprt(unknown, c2_sym);
      auto rhs_expr = equal_exprt(c3_sym, c4_sym);

      auto or_expr = or_exprt(lhs_expr, rhs_expr);

      ASSUME_TRUE(environment, or_expr, ns);
    }
    WHEN("unknown == { 2, 3 } || { 3, 4 } != { 4, 5 }")
    {
      auto unknown = symbol_exprt("unknown", v23->type());
      auto lhs_expr = equal_exprt(unknown, c2_sym);
      auto rhs_expr = notequal_exprt(c3_sym, c4_sym);

      auto or_expr = or_exprt(lhs_expr, rhs_expr);

      ASSUME_NIL(environment, or_expr, ns);
    }
    WHEN("{ 1, 2 } == { 4, 5 } || { 3, 4 } == { 1, 2 }")
    {
      auto expr0 = equal_exprt(c1_sym, c4_sym);
      auto expr1 = equal_exprt(c3_sym, c1_sym);

      auto or_expr = or_exprt(expr0, expr1);

      ASSUME_FALSE(environment, or_expr, ns);
    }
  }
}

void ASSUME_TRUE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  THEN("assume is true")
  {
    auto assumption = env.do_assume(expr, ns);
    REQUIRE(assumption.id() != ID_nil);
    REQUIRE(assumption.type().id() == ID_bool);
    REQUIRE(assumption.is_true());
  }
}

void ASSUME_FALSE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  THEN("assume is false")
  {
    auto assumption = env.do_assume(expr, ns);
    REQUIRE(assumption.id() != ID_nil);
    REQUIRE(assumption.type().id() == ID_bool);
    REQUIRE(assumption.is_false());
  }
}

void ASSUME_NIL(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  THEN("assume is nil")
  {
    auto assumption = env.do_assume(expr, ns);
    REQUIRE(assumption.id() == ID_nil);
  }
}

std::vector<std::string>
split(std::string const &s, std::string const &delimiter)
{
  std::vector<std::string> tokens;

  size_t pos = 0;
  size_t end = 0;
  while(end != s.size())
  {
    end = s.find(delimiter, pos);
    end = (end != std::string::npos) ? end : s.size();
    tokens.push_back(s.substr(pos, end - pos));
    pos = end + delimiter.size();
  }

  return tokens;
}

std::vector<exprt> numbersToExprs(std::vector<std::string> const &numbers)
{
  auto type = signedbv_typet(32);
  auto exprs = std::vector<exprt>{};
  for(auto number : numbers)
  {
    auto n = std::stoi(number);
    exprs.push_back(from_integer(n, type));
  }
  return exprs;
}
