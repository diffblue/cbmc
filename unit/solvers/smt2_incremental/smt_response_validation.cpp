// Author: Diffblue Ltd.

#include <testing-utils/smt2irep.h>
#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_response_validation.h>

// Debug printer for `smt_responset`. This will be used by the catch framework
// for printing in the case of failed checks / requirements.
std::ostream &
operator<<(std::ostream &output_stream, const smt_responset &response)
{
  output_stream << response.pretty();
  return output_stream;
}

TEST_CASE("response_or_errort storage", "[core][smt2_incremental]")
{
  SECTION("Error response")
  {
    const std::string message{"Test error message"};
    const response_or_errort<smt_responset> error{message};
    CHECK_FALSE(error.get_if_valid());
    CHECK(*error.get_if_error() == std::vector<std::string>{message});
  }
  SECTION("Valid response")
  {
    const response_or_errort<smt_responset> valid{smt_unsupported_responset{}};
    CHECK_FALSE(valid.get_if_error());
    CHECK(*valid.get_if_valid() == smt_unsupported_responset{});
  }
}

TEST_CASE("Validation of check-sat repsonses", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(*smt2irep("sat").parsed_output).get_if_valid() ==
    smt_check_sat_responset{smt_sat_responset{}});
  CHECK(
    *validate_smt_response(*smt2irep("unsat").parsed_output).get_if_valid() ==
    smt_check_sat_responset{smt_unsat_responset{}});
  CHECK(
    *validate_smt_response(*smt2irep("unknown").parsed_output).get_if_valid() ==
    smt_check_sat_responset{smt_unknown_responset{}});
}

TEST_CASE("Validation of SMT success response", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(*smt2irep("success").parsed_output).get_if_valid() ==
    smt_success_responset{});
}

TEST_CASE("Validation of SMT unsupported response", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(*smt2irep("unsupported").parsed_output)
       .get_if_valid() == smt_unsupported_responset{});
}

TEST_CASE(
  "Error handling of SMT response validation",
  "[core][smt2_incremental]")
{
  SECTION("Parse tree produced is not a valid SMT-LIB version 2.6 response")
  {
    const response_or_errort<smt_responset> validation_response =
      validate_smt_response(*smt2irep("foobar").parsed_output);
    CHECK(
      *validation_response.get_if_error() ==
      std::vector<std::string>{"Invalid SMT response \"foobar\""});
    CHECK(
      *validate_smt_response(*smt2irep("()").parsed_output).get_if_error() ==
      std::vector<std::string>{"Invalid SMT response \"\""});
  }
}
