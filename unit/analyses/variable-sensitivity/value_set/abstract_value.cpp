/*******************************************************************\

Module: Unit tests for value set abstract values

Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_test_common.h"
#include <analyses/variable-sensitivity/value_set_abstract_value.h>
#include <ansi-c/expr2c.h>

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
      oss << expr2c(value, ns);
    }
    oss << " }";
    return oss.str();
  }
};
} // namespace

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
  auto const value_set = value_set_abstract_valuet{type, {}};
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
