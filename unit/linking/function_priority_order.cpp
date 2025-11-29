// Author: Michael Tautschnig

/// \file
/// Unit tests for order_functions_by_priority

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include <linking/function_priority_order.h>
#include <testing-utils/use_catch.h>

static symbolt function(const irep_idt &name, std::optional<unsigned> priority)
{
  typet return_type{ID_constructor};
  if(priority.has_value())
    return_type.add(ID_priority, from_integer(*priority, unsignedbv_typet{32}));
  symbolt symbol{name, code_typet{{}, return_type}, ID_C};
  return symbol;
}

static std::vector<irep_idt>
names(const std::vector<std::reference_wrapper<const symbolt>> &symbols)
{
  std::vector<irep_idt> result;
  for(const auto &symbol : symbols)
    result.push_back(symbol.get().name);
  return result;
}

TEST_CASE("order_functions_by_priority", "[core][linking]")
{
  const symbolt none1 = function("none1", std::nullopt);
  const symbolt none2 = function("none2", std::nullopt);
  const symbolt p65535 = function("p65535", 65535);
  const symbolt p101 = function("p101", 101);
  const symbolt p200 = function("p200", 200);
  const symbolt p200b = function("p200b", 200);

  const std::vector<std::reference_wrapper<const symbolt>> functions = {
    none1, p200, none2, p65535, p101, p200b};

  SECTION("Default priority")
  {
    REQUIRE(function_priority(none1) == DEFAULT_FUNCTION_PRIORITY);
    REQUIRE(function_priority(p101) == 101);
  }

  SECTION("Constructors: ascending priority, ties in the given order")
  {
    // as in GCC, an explicit priority of 65535 is the same as no priority
    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::ASCENDING)) ==
      std::vector<irep_idt>{
        "p101", "p200", "p200b", "none1", "none2", "p65535"});
  }

  SECTION("Destructors: the exact reverse of constructors")
  {
    CHECK(
      names(order_functions_by_priority(
        functions, function_priority_ordert::DESCENDING)) ==
      std::vector<irep_idt>{
        "p65535", "none2", "none1", "p200b", "p200", "p101"});
  }
}
