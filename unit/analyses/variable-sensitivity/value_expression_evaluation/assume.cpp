/*******************************************************************\

 Module: Unit tests for abstract_value_objectt::expression_transform

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

template <class expression_type>
exprt binary_expression(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto op1_sym = symbol_exprt("op1", op1->type());
  auto op2_sym = symbol_exprt("op2", op2->type());
  environment.assign(op1_sym, op1, ns);
  environment.assign(op2_sym, op2, ns);

  return expression_type(op1_sym, op2_sym);
}

static void ASSUME_TRUE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);
static void ASSUME_FALSE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);

std::vector<std::string>
split(std::string const &s, std::string const &delimiter);
std::vector<exprt> numbersToExprs(std::vector<std::string> const &numbers);

class assume_tester
{
public:
  void operator()(bool is_true, std::vector<std::string> const &tests)
  {
    for(auto test : tests)
    {
      if(is_test(test, "=="))
        test_fn<equal_exprt>(is_true, test, "==");
      else if(is_test(test, "!="))
        test_fn<notequal_exprt>(is_true, test, "!=");
      else
        FAIL("Unknown test: " + test);
    }
  }

  bool is_test(std::string const &test, std::string const &delimiter)
  {
    return test.find(delimiter) != std::string::npos;
  }

  template <class expression_type>
  void
  test_fn(bool is_true, std::string const &test, std::string const &delimiter)
  {
    WHEN(test)
    {
      auto operands = split(test, delimiter);
      REQUIRE(operands.size() == 2);

      auto op1 = build_op(operands[0]);
      auto op2 = build_op(operands[1]);

      auto equals =
        binary_expression<expression_type>(op1, op2, environment, ns);

      if(is_true)
        ASSUME_TRUE(environment, equals, ns);
      else
        ASSUME_FALSE(environment, equals, ns);
    }
  }

  assume_tester(abstract_environmentt &env, namespacet &n)
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

  assume_tester assumeTester(environment, ns);

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
}

void ASSUME_TRUE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  THEN("assume is true")
  {
    auto assumption = env.do_assume(expr, ns, true);
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
    auto assumption = env.do_assume(expr, ns, true);
    REQUIRE(assumption.id() != ID_nil);
    REQUIRE(assumption.type().id() == ID_bool);
    REQUIRE(assumption.is_false());
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
  const typet type = signedbv_typet(32);
  auto exprs = std::vector<exprt>{};
  for(auto number : numbers)
  {
    auto n = std::stoi(number);
    exprs.push_back(from_integer(n, type));
  }
  return exprs;
}
