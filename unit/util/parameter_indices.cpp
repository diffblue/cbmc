/*******************************************************************\

 Module: Parameter indices test

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <util/std_types.h>

void check_consistency(const symbolt &symbol)
{
  const auto &code_type = to_code_type(symbol.type);
  auto parameter_ids = code_type.parameter_identifiers();
  auto parameter_indices = code_type.parameter_indices();

  REQUIRE(parameter_ids.size() == parameter_indices.size());
  for(std::size_t i = 0; i < parameter_ids.size(); ++i)
    REQUIRE(parameter_indices.at(parameter_ids.at(i)) == i);
}

TEST_CASE("Parameter indices consistency", "[core][util][parameter_indices]")
{
  symbol_tablet symbol_table = load_java_class("ParameterIndicesTest", "util/");
  check_consistency(
    symbol_table.lookup_ref(
      "java::ParameterIndicesTest.f:(LParameterIndicesTest;I)V"));
  check_consistency(
    symbol_table.lookup_ref(
      "java::ParameterIndicesTest.g:(FLParameterIndicesTest;)V"));
}
