/*******************************************************************\

Module: Parameter indices test

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_types.h>

#include <java-testing-utils/load_java_class.h>
#include <testing-utils/use_catch.h>

void check_consistency(const symbolt &symbol)
{
  const auto &method_type = to_java_method_type(symbol.type);
  auto parameter_ids = method_type.parameter_identifiers();
  auto parameter_indices = method_type.parameter_indices();

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
