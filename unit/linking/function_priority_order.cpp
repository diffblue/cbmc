// Author: Daniel Kroening, kroening@kroening.com

/// \file
/// Unit tests for order_functions_by_priority

#include <util/symbol.h>

#include <linking/function_priority_order.h>
#include <testing-utils/use_catch.h>

#include <vector>

static std::vector<irep_idt>
names(const std::list<std::reference_wrapper<const symbolt>> &symbols)
{
  std::vector<irep_idt> result;
  for(const auto &symbol : symbols)
    result.push_back(symbol.get().name);
  return result;
}

TEST_CASE("order_functions_by_priority", "[core][linking]")
{
  using entryt =
    std::pair<std::reference_wrapper<const symbolt>, std::optional<mp_integer>>;

  symbolt none1, none2, p100, p200;
  none1.name = "none1";
  none2.name = "none2";
  p100.name = "p100";
  p200.name = "p200";

  SECTION("ascending: ascending priority, unprioritised last (constructors)")
  {
    const std::list<entryt> functions = {
      {std::cref(none1), std::nullopt},
      {std::cref(p200), mp_integer{200}},
      {std::cref(p100), mp_integer{100}},
      {std::cref(none2), std::nullopt}};

    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::ASCENDING)) ==
      std::vector<irep_idt>{"p100", "p200", "none1", "none2"});
  }

  SECTION("descending: unprioritised first, then descending (destructors)")
  {
    const std::list<entryt> functions = {
      {std::cref(none1), std::nullopt},
      {std::cref(p100), mp_integer{100}},
      {std::cref(p200), mp_integer{200}}};

    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::DESCENDING)) ==
      std::vector<irep_idt>{"none1", "p200", "p100"});
  }

  SECTION("descending order between two priorities")
  {
    // Two prioritised functions must come out in descending priority order;
    // this is the case the end-to-end regression test now also exercises.
    symbolt p201, p202;
    p201.name = "p201";
    p202.name = "p202";

    const std::list<entryt> functions = {
      {std::cref(p201), mp_integer{201}}, {std::cref(p202), mp_integer{202}}};

    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::DESCENDING)) ==
      std::vector<irep_idt>{"p202", "p201"});
  }

  SECTION("functions sharing a priority preserve source order")
  {
    symbolt a, b;
    a.name = "a";
    b.name = "b";

    const std::list<entryt> functions = {
      {std::cref(a), mp_integer{5}}, {std::cref(b), mp_integer{5}}};

    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::ASCENDING)) ==
      std::vector<irep_idt>{"a", "b"});
    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::DESCENDING)) ==
      std::vector<irep_idt>{"a", "b"});
  }
}
