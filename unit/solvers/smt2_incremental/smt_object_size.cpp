// Author: Diffblue Ltd.

#include <util/c_types.h>
#include <util/config.h>

#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_object_size.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Test smt_object_sizet", "[core][smt2_incremental]")
{
  const std::size_t object_bits = GENERATE(8, 16);
  INFO("Using " + std::to_string(object_bits) + " object id bits.");
  // Configuration needs to be set because smt_object_sizet is based on it.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();
  config.bv_encoding.object_bits = object_bits;
  const smt_object_sizet object_size;
  const std::size_t size_bits = size_type().get_width();
  SECTION("Declare function")
  {
    CHECK(
      object_size.declaration ==
      smt_declare_function_commandt{
        smt_identifier_termt{"size_of_object", smt_bit_vector_sortt{size_bits}},
        {smt_bit_vector_sortt{object_bits}}});
  }
  SECTION("Apply function")
  {
    const smt_identifier_termt object_id{
      "foo", smt_bit_vector_sortt{object_bits}};
    const smt_function_application_termt function_application =
      object_size.make_application(std::vector<smt_termt>{object_id});
    CHECK(
      function_application.function_identifier() ==
      smt_identifier_termt{"size_of_object", smt_bit_vector_sortt{size_bits}});
    REQUIRE(function_application.arguments().size() == 1);
    REQUIRE(function_application.arguments().at(0).get() == object_id);
  }
  SECTION("Define result")
  {
    const smt_bit_vector_constant_termt size_term{2, size_bits};
    const smt_commandt definition = object_size.make_definition(42, size_term);
    CHECK(
      definition == smt_assert_commandt{smt_core_theoryt::equal(
                      object_size.make_application(std::vector<smt_termt>{
                        smt_bit_vector_constant_termt{42, object_bits}}),
                      size_term)});
  }
}
