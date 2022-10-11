// Author: Diffblue Ltd.

#include <util/c_types.h>
#include <util/config.h>

#include <solvers/smt2_incremental/smt_is_dynamic_object.h>
#include <solvers/smt2_incremental/theories/smt_core_theory.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Test smt_is_dynamic_objectt", "[core][smt2_incremental]")
{
  const std::size_t object_bits = GENERATE(8, 16);
  INFO("Using " + std::to_string(object_bits) + " object id bits.");
  // Configuration needs to be set because smt_is_dynamic_objectt uses it.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();
  config.bv_encoding.object_bits = object_bits;
  const smt_is_dynamic_objectt is_dynamic_object;
  SECTION("Declare function")
  {
    CHECK(
      is_dynamic_object.declaration ==
      smt_declare_function_commandt{
        smt_identifier_termt{"is_dynamic_object", smt_bool_sortt{}},
        {smt_bit_vector_sortt{object_bits}}});
  }
  SECTION("Apply function")
  {
    const smt_identifier_termt object_id{
      "foo", smt_bit_vector_sortt{object_bits}};
    const smt_function_application_termt function_application =
      is_dynamic_object.make_application(std::vector<smt_termt>{object_id});
    CHECK(
      function_application.function_identifier() ==
      smt_identifier_termt{"is_dynamic_object", smt_bool_sortt{}});
    REQUIRE(function_application.arguments().size() == 1);
    REQUIRE(function_application.arguments().at(0).get() == object_id);
  }
  SECTION("Define result")
  {
    const bool dynamic_status = GENERATE(true, false);
    INFO(
      "Testing for dynamic status of " +
      std::string(dynamic_status ? "true" : "false"));
    const smt_commandt definition =
      is_dynamic_object.make_definition(42, dynamic_status);
    CHECK(
      definition == smt_assert_commandt{smt_core_theoryt::equal(
                      is_dynamic_object.make_application(std::vector<smt_termt>{
                        smt_bit_vector_constant_termt{42, object_bits}}),
                      smt_bool_literal_termt{dynamic_status})});
  }
}
