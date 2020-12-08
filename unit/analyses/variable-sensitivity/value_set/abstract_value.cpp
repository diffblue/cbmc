/*******************************************************************\

Module: Unit tests for value set abstract values

Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_test_common.h"
#include <analyses/ai.h>
#include <analyses/variable-sensitivity/value_set_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>
#include <ansi-c/expr2c.h>

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <sstream>
#include <string>
#include <util/arith_tools.h>
#include <vector>

namespace
{
// NOLINTNEXTLINE(readability/identifiers)
class ContainsAllOf
  : public Catch::MatcherBase<value_set_abstract_valuet::valuest>
{
private:
  std::vector<exprt> should_contain_values;

public:
  template <typename... Args>
  explicit ContainsAllOf(Args &&... should_contain_values)
    : should_contain_values{std::forward<Args>(should_contain_values)...}
  {
  }

  bool match(const value_set_abstract_valuet::valuest &values) const override
  {
    for(auto const &value : should_contain_values)
    {
      if(values.count(value) == 0)
      {
        return false;
      }
    }
    return true;
  }

  std::string describe() const override
  {
    std::ostringstream oss{};
    auto const ns = namespacet{symbol_tablet{}};
    oss << "contains all of { ";
    bool first = true;
    for(auto const &value : should_contain_values)
    {
      if(!first)
      {
        oss << ", ";
      }
      first = false;
      oss << expr2c(value, ns);
    }
    oss << " }";
    return oss.str();
  }
};
} // namespace

std::unique_ptr<variable_sensitivity_domain_factoryt> domain_factory()
{
  auto configuration = vsd_configt{};
  auto vs_object_factory =
    std::make_shared<variable_sensitivity_object_factoryt>(configuration);

  return util_make_unique<variable_sensitivity_domain_factoryt>(
    vs_object_factory, configuration);
}

TEST_CASE(
  "A value set abstract object created from type is top",
  VALUE_SET_TEST_TAGS)
{
  value_set_abstract_valuet abstract_value(signedbv_typet{32});
  REQUIRE(abstract_value.is_top());
  REQUIRE(!abstract_value.is_bottom());
}

TEST_CASE(
  "A value set created from a single value represents that value",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value = from_integer(10, type);
  auto const value_set = value_set_abstract_valuet{type, {value}};

  REQUIRE(!value_set.is_top());
  REQUIRE(!value_set.is_bottom());
  REQUIRE(value_set.get_values().size() == 1);
  REQUIRE_THAT(value_set.get_values(), ContainsAllOf{value});
}

TEST_CASE(
  "A value set created from multiple values represents all of them",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value1 = from_integer(10, type);
  auto const value2 = from_integer(36, type);
  auto const value3 = from_integer(42, type);
  auto const value_set =
    value_set_abstract_valuet{type, {value1, value2, value3}};

  REQUIRE(!value_set.is_top());
  REQUIRE(!value_set.is_bottom());
  REQUIRE(value_set.get_values().size() == 3);
  REQUIRE_THAT(value_set.get_values(), ContainsAllOf(value1, value2, value3));
}

TEST_CASE(
  "A value set created from an empty set is bottom",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value_set =
    value_set_abstract_valuet{type, value_set_abstract_valuet::valuest{}};
  REQUIRE(!value_set.is_top());
  REQUIRE(value_set.is_bottom());
}

TEST_CASE(
  "A value set created with too many elements is TOP",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto values = value_set_abstract_valuet::valuest{};
  for(std::size_t i = 0; i <= value_set_abstract_valuet::max_value_set_size;
      ++i)
  {
    values.insert(from_integer(i, type));
  }
  auto const value_set = value_set_abstract_valuet{type, values};

  REQUIRE(value_set.is_top());
  REQUIRE(!value_set.is_bottom());
}

TEST_CASE(
  "A value set created by merging two single value-value sets contains both "
  "values",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value1 = from_integer(10, type);
  auto const value2 = from_integer(42, type);
  using valuest = value_set_abstract_valuet::valuest;
  auto const value_set1 =
    std::make_shared<value_set_abstract_valuet>(type, valuest{value1});
  auto const value_set2 =
    std::make_shared<value_set_abstract_valuet>(type, valuest{value2});

  bool out_modifications;
  auto const merged_abstract_object =
    abstract_objectt::merge(value_set1, value_set2, out_modifications);
  auto const merged_value_set =
    std::dynamic_pointer_cast<const value_set_abstract_valuet>(
      merged_abstract_object);

  REQUIRE(merged_value_set != nullptr);
  REQUIRE(!merged_value_set->is_top());
  REQUIRE(!merged_value_set->is_bottom());
  REQUIRE(merged_value_set->get_values().size() == 2);
  REQUIRE_THAT(merged_value_set->get_values(), ContainsAllOf(value1, value2));
}

TEST_CASE(
  "A value set created by merging two multi-value value sets contains all "
  "values from both of them",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value1 = from_integer(10, type);
  auto const value2 = from_integer(20, type);
  auto const value3 = from_integer(30, type);
  using valuest = value_set_abstract_valuet::valuest;
  auto const value_set1 =
    std::make_shared<value_set_abstract_valuet>(type, valuest{value1, value2});
  auto const value_set2 =
    std::make_shared<value_set_abstract_valuet>(type, valuest{value2, value3});

  bool out_modifications;
  auto const merged_abstracted_object =
    abstract_objectt::merge(value_set1, value_set2, out_modifications);
  auto const merged_value_set =
    std::dynamic_pointer_cast<const value_set_abstract_valuet>(
      merged_abstracted_object);

  REQUIRE(merged_value_set != nullptr);
  REQUIRE(!merged_value_set->is_top());
  REQUIRE(!merged_value_set->is_bottom());
  REQUIRE(merged_value_set->get_values().size() == 3);
  REQUIRE_THAT(
    merged_value_set->get_values(), ContainsAllOf(value1, value2, value3));
}

TEST_CASE(
  "The result of merging two value sets is TOP if both are non-top value sets "
  "and the resulting set would have too many elements",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  using valuest = value_set_abstract_valuet::valuest;
  auto values = valuest{};
  for(std::size_t i = 0; i < value_set_abstract_valuet::max_value_set_size; ++i)
  {
    values.insert(from_integer(i, type));
  }

  auto const straw_that_broke_the_camels_back =
    from_integer(value_set_abstract_valuet::max_value_set_size, type);

  auto const value_set1 =
    std::make_shared<value_set_abstract_valuet>(type, values);
  REQUIRE(!value_set1->is_top());

  auto const value_set2 = std::make_shared<value_set_abstract_valuet>(
    type, valuest{straw_that_broke_the_camels_back});
  REQUIRE(!value_set2->is_top());

  bool out_modifications;
  auto const merged_abstract_object =
    abstract_objectt::merge(value_set1, value_set2, out_modifications);
  auto const merged_value_set =
    std::dynamic_pointer_cast<const value_set_abstract_valuet>(
      merged_abstract_object);

  REQUIRE(merged_value_set != nullptr);
  REQUIRE(merged_value_set->is_top());
  REQUIRE(!merged_value_set->is_bottom());
}

TEST_CASE(
  "The result of merging two value sets is top if one of them is TOP",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value = from_integer(10, type);
  using valuest = value_set_abstract_valuet::valuest;
  auto const value_set1 =
    std::make_shared<value_set_abstract_valuet>(type, valuest{value});
  auto const value_set2 = std::make_shared<value_set_abstract_valuet>(type);

  bool out_modifications;
  auto const merged_abstract_object =
    abstract_objectt::merge(value_set1, value_set2, out_modifications);

  REQUIRE(merged_abstract_object->is_top());
  REQUIRE(!merged_abstract_object->is_bottom());
}

TEST_CASE(
  "Make sure the output method works correctly with a value set with 0 "
  "elements",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value_set =
    value_set_abstract_valuet{type, value_set_abstract_valuet::valuest{}};

  const ait<variable_sensitivity_domaint> ai{domain_factory()};

  std::stringstream ss;
  value_set.output(ss, ai, namespacet{symbol_tablet{}});
  REQUIRE(ss.str() == "BOTTOM");
}

TEST_CASE(
  "Make sure the output method works correctly with a value set with 1 element",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value = from_integer(10, type);
  auto const value_set = value_set_abstract_valuet{type, {value}};

  const ait<variable_sensitivity_domaint> ai{domain_factory()};

  std::stringstream ss;
  value_set.output(ss, ai, namespacet{symbol_tablet{}});
  REQUIRE(ss.str() == "{ 10 }");
}

TEST_CASE(
  "Make sure the output method works correctly with a value set with 3 "
  "elements",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value1 = from_integer(10, type);
  auto const value2 = from_integer(12, type);
  auto const value3 = from_integer(14, type);
  auto const value_set =
    value_set_abstract_valuet{type, {value1, value2, value3}};

  const ait<variable_sensitivity_domaint> ai{domain_factory()};

  std::stringstream ss;
  value_set.output(ss, ai, namespacet{symbol_tablet{}});
  REQUIRE(ss.str() == "{ 10 12 14 }");
}

TEST_CASE(
  "Make sure that the output method works with a TOP value set",
  VALUE_SET_TEST_TAGS)
{
  // Build and ensure value set is TOP
  auto const type = signedbv_typet{32};
  auto values = value_set_abstract_valuet::valuest{};
  for(std::size_t i = 0; i <= value_set_abstract_valuet::max_value_set_size;
      ++i)
  {
    values.insert(from_integer(i, type));
  }
  auto const value_set = value_set_abstract_valuet{type, values};
  REQUIRE(value_set.is_top());

  const ait<variable_sensitivity_domaint> ai{domain_factory()};

  std::stringstream ss;
  value_set.output(ss, ai, namespacet{symbol_tablet{}});
  REQUIRE(ss.str() == "TOP");
}

TEST_CASE(
  "Value set abstract value that is TOP can not be turned into a constant",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value_set = value_set_abstract_valuet{type};

  REQUIRE(value_set.to_constant() == nil_exprt{});
}

TEST_CASE(
  "Value set abstract value that is bottom can not be turned into a constant",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value_set =
    value_set_abstract_valuet{type, value_set_abstract_valuet::valuest{}};

  REQUIRE(value_set.to_constant() == nil_exprt{});
}

TEST_CASE(
  "Value set with multiple possible values can not be turned into a constant",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto values = value_set_abstract_valuet::valuest{};
  values.insert(from_integer(0, type));
  values.insert(from_integer(1, type));
  auto const value_set = value_set_abstract_valuet{type, values};

  REQUIRE(value_set.to_constant() == nil_exprt{});
}

TEST_CASE(
  "Value set with exactly one possible value can be turned into a constant",
  VALUE_SET_TEST_TAGS)
{
  auto const type = signedbv_typet{32};
  auto const value = from_integer(0, type);
  auto const value_set =
    value_set_abstract_valuet{type, value_set_abstract_valuet::valuest{value}};

  REQUIRE(value_set.to_constant() == value);
}

static abstract_environmentt get_value_set_abstract_environment()
{
  vsd_configt config;
  config.value_abstract_type = VALUE_SET;
  config.advanced_sensitivities.new_value_set = true;
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  auto environment = abstract_environmentt{object_factory};
  environment.make_top();
  return environment;
}

TEST_CASE("Eval on an constant gives us that constant", VALUE_SET_TEST_TAGS)
{
  const auto environment = get_value_set_abstract_environment();
  namespacet ns{symbol_tablet{}};
  const auto zero = from_integer(0, signedbv_typet{32});
  const auto eval_result = environment.eval(zero, ns);
  REQUIRE(eval_result != nullptr);
  REQUIRE(!eval_result->is_top());
  REQUIRE(!eval_result->is_bottom());
  const auto eval_result_as_value_set =
    std::dynamic_pointer_cast<const value_set_abstract_valuet>(
      eval_result->unwrap_context());
  REQUIRE(eval_result_as_value_set != nullptr);
  REQUIRE(eval_result_as_value_set->get_values().size() == 1);
  REQUIRE_THAT(eval_result_as_value_set->get_values(), ContainsAllOf{zero});
}

TEST_CASE(
  "Eval on a plus expression with constant operands gives us the result of "
  "that plus",
  VALUE_SET_TEST_TAGS)
{
  const auto environment = get_value_set_abstract_environment();
  namespacet ns{symbol_tablet{}};
  const auto s32_type = signedbv_typet{32};
  const auto three = from_integer(3, s32_type);
  const auto five = from_integer(5, s32_type);
  const auto three_plus_five = plus_exprt{three, five};

  auto eval_result = environment.eval(three_plus_five, ns);
  REQUIRE(eval_result != nullptr);
  REQUIRE(!eval_result->is_top());
  REQUIRE(!eval_result->is_bottom());

  const auto eval_result_as_value_set =
    std::dynamic_pointer_cast<const value_set_abstract_valuet>(
      eval_result->unwrap_context());
  REQUIRE(eval_result_as_value_set != nullptr);
  const auto eight = from_integer(8, s32_type);
  REQUIRE(eval_result_as_value_set->get_values().size() == 1);
  REQUIRE_THAT(eval_result_as_value_set->get_values(), ContainsAllOf{eight});
}

TEST_CASE(
  "Eval on a multiply expression on symbols gives us the results of that "
  "multiplication",
  VALUE_SET_TEST_TAGS)
{
  auto environment = get_value_set_abstract_environment();
  symbol_tablet symbol_table;

  const auto s32_type = signedbv_typet{32};

  symbolt a_symbol{};
  a_symbol.name = a_symbol.pretty_name = a_symbol.base_name = "a";
  a_symbol.is_lvalue = true;
  a_symbol.type = s32_type;
  symbol_table.add(a_symbol);

  symbolt b_symbol{};
  b_symbol.name = b_symbol.pretty_name = b_symbol.base_name = "b";
  b_symbol.is_lvalue = true;
  b_symbol.type = s32_type;
  symbol_table.add(b_symbol);
  symbol_table.add(b_symbol);

  const namespacet ns{symbol_table};

  const auto three = from_integer(3, s32_type);
  const auto four = from_integer(4, s32_type);
  const auto five = from_integer(5, s32_type);
  const auto six = from_integer(6, s32_type);

  const auto three_or_five = std::make_shared<const value_set_abstract_valuet>(
    s32_type, value_set_abstract_valuet::valuest{three, five});
  environment.assign(a_symbol.symbol_expr(), three_or_five, ns);

  const auto four_or_six = std::make_shared<const value_set_abstract_valuet>(
    s32_type, value_set_abstract_valuet::valuest{four, six});
  environment.assign(b_symbol.symbol_expr(), four_or_six, ns);

  const auto a_times_b =
    mult_exprt{a_symbol.symbol_expr(), b_symbol.symbol_expr()};

  const auto eval_result = environment.eval(a_times_b, ns);
  REQUIRE(eval_result != nullptr);
  REQUIRE(!eval_result->is_top());
  REQUIRE(!eval_result->is_bottom());

  const auto eval_result_as_value_set =
    std::dynamic_pointer_cast<const value_set_abstract_valuet>(
      eval_result->unwrap_context());
  REQUIRE(eval_result_as_value_set != nullptr);
  REQUIRE(eval_result_as_value_set->get_values().size() == 4);

  const auto twelve = from_integer(12, s32_type);
  const auto eighteen = from_integer(18, s32_type);
  const auto twenty = from_integer(20, s32_type);
  const auto twentyfour = from_integer(30, s32_type);
  REQUIRE_THAT(
    eval_result_as_value_set->get_values(),
    ContainsAllOf(twelve, eighteen, twenty, twentyfour));
}
