// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_responses.h>
#include <util/mp_arith.h>

TEST_CASE("Test smt success response", "[core][smt2_incremental]")
{
  const smt_responset success{smt_success_responset{}};
  CHECK(success.cast<smt_success_responset>());
  CHECK_FALSE(success.cast<smt_error_responset>());
}

TEST_CASE(
  "Check sat response kind instantiation and comparisons.",
  "[core][smt2_incremental]")
{
  const smt_check_sat_response_kindt sat = smt_sat_responset{};
  const smt_check_sat_response_kindt unsat = smt_unsat_responset{};
  const smt_check_sat_response_kindt unknown = smt_unknown_responset{};
  SECTION("Comparisons")
  {
    CHECK(sat == smt_sat_responset{});
    CHECK(sat != unsat);
    CHECK(sat != unknown);
    CHECK(unsat == smt_unsat_responset{});
    CHECK(unsat != sat);
    CHECK(unsat != unknown);
    CHECK(unknown == smt_unknown_responset{});
    CHECK(unknown != sat);
    CHECK(unknown != unsat);
  }
  SECTION("Casts")
  {
    CHECK(sat.cast<smt_sat_responset>());
    CHECK_FALSE(sat.cast<smt_unsat_responset>());
    CHECK_FALSE(sat.cast<smt_unknown_responset>());
  }
}

TEMPLATE_TEST_CASE(
  "Check sat response instantiation, casting and getter",
  "[core][smt2_incremental]",
  smt_sat_responset,
  smt_unsat_responset,
  smt_unknown_responset)
{
  const smt_responset check_sat = smt_check_sat_responset{TestType{}};
  CHECK_FALSE(check_sat.cast<smt_error_responset>());
  CHECK(check_sat.cast<smt_check_sat_responset>()->kind() == TestType{});
}

TEST_CASE(
  "Test smt_get_value_response pair storage.",
  "[core][smt2_incremental]")
{
  const smt_bit_vector_sortt sort{8};
  const smt_bit_vector_constant_termt one{1, sort};
  const smt_bit_vector_constant_termt two{2, sort};
  const smt_get_value_responset::valuation_pairt pair1{
    smt_identifier_termt{"foo", sort}, one};
  const smt_get_value_responset::valuation_pairt pair2{
    smt_identifier_termt{"bar", sort}, two};
  SECTION("Valuation pair getters.")
  {
    REQUIRE(pair1.descriptor() == smt_identifier_termt{"foo", sort});
    REQUIRE(pair1.value() == one);
    REQUIRE(pair2.descriptor() == smt_identifier_termt{"bar", sort});
    REQUIRE(pair2.value() == two);
  }
  SECTION("Valuation pair comparisons.")
  {
    REQUIRE(
      pair1 == smt_get_value_responset::valuation_pairt{
                 smt_identifier_termt{"foo", sort}, one});
    REQUIRE(
      pair1 != smt_get_value_responset::valuation_pairt{
                 smt_identifier_termt{"bar", sort}, one});
    REQUIRE(
      pair1 != smt_get_value_responset::valuation_pairt{
                 smt_identifier_termt{"foo", sort}, two});
  }
  SECTION("Missing valuation pair(s).")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_get_value_responset{{}});
  }
  SECTION("Single valuation pair.")
  {
    const smt_get_value_responset one_pair_response{{pair1}};
    REQUIRE(one_pair_response.pairs().size() == 1);
    REQUIRE(one_pair_response.pairs().at(0).get() == pair1);
  }
  SECTION("Multiple valuation pairs.")
  {
    const smt_get_value_responset multi_pair_response{{pair1, pair2}};
    REQUIRE(multi_pair_response.pairs().size() == 2);
    REQUIRE(multi_pair_response.pairs().at(0).get() == pair1);
    REQUIRE(multi_pair_response.pairs().at(1).get() == pair2);
  }
}

TEST_CASE("Test smt unsupported response", "[core][smt2_incremental]")
{
  const smt_responset success{smt_unsupported_responset{}};
  CHECK(success.cast<smt_unsupported_responset>());
  CHECK_FALSE(success.cast<smt_error_responset>());
}

TEST_CASE("Test error response.", "[core][smt2_incremental]")
{
  const irep_idt message{"Test error message"};
  const smt_error_responset error{message};
  SECTION("message getter")
  {
    CHECK(error.message() == message);
  }
  SECTION("casting")
  {
    const smt_responset upcast{error};
    CHECK(upcast.cast<smt_error_responset>());
    CHECK_FALSE(upcast.cast<smt_success_responset>());
  }
}

TEST_CASE("SMT response comparisons.", "[core][smt2_incremental]")
{
  const smt_check_sat_responset sat{smt_sat_responset{}};
  CHECK(sat == smt_check_sat_responset{smt_sat_responset{}});
  CHECK(sat != smt_check_sat_responset{smt_unsat_responset{}});
  const smt_error_responset error{"Test error"};
  CHECK(sat != error);
  CHECK(error == smt_error_responset{"Test error"});
  CHECK(error != smt_error_responset{"Other error"});
}
