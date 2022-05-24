// Author: Diffblue Ltd.

#include <testing-utils/smt2irep.h>
#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_response_validation.h>
#include <util/mp_arith.h>

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

TEST_CASE("Validation of SMT error response", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(
       *smt2irep("(error \"Test error message.\")").parsed_output)
       .get_if_valid() == smt_error_responset{"Test error message."});
  CHECK(
    *validate_smt_response(*smt2irep("(error)").parsed_output).get_if_error() ==
    std::vector<std::string>{"Error response is missing the error message."});
  CHECK(
    *validate_smt_response(
       *smt2irep("(error \"Test error message1.\" \"Test error message2.\")")
          .parsed_output)
       .get_if_error() ==
    std::vector<std::string>{"Error response has multiple error messages - \"\n"
                             "0: error\n"
                             "1: Test error message1.\n"
                             "2: Test error message2.\"."});
}

TEST_CASE("smt get-value response validation", "[core][smt2_incremental]")
{
  SECTION("Boolean sorted values.")
  {
    const response_or_errort<smt_responset> true_response =
      validate_smt_response(*smt2irep("((a true))").parsed_output);
    CHECK(
      *true_response.get_if_valid() ==
      smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
        smt_identifier_termt{"a", smt_bool_sortt{}},
        smt_bool_literal_termt{true}}}});
    const response_or_errort<smt_responset> false_response =
      validate_smt_response(*smt2irep("((a false))").parsed_output);
    CHECK(
      *false_response.get_if_valid() ==
      smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
        smt_identifier_termt{"a", smt_bool_sortt{}},
        smt_bool_literal_termt{false}}}});
  }
  SECTION("Bit vector sorted values.")
  {
    SECTION("Hex value")
    {
      const response_or_errort<smt_responset> response_255 =
        validate_smt_response(*smt2irep("((a #xff))").parsed_output);
      CHECK(
        *response_255.get_if_valid() ==
        smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
          smt_identifier_termt{"a", smt_bit_vector_sortt{8}},
          smt_bit_vector_constant_termt{255, 8}}}});
    }
    SECTION("Binary value")
    {
      const response_or_errort<smt_responset> response_42 =
        validate_smt_response(*smt2irep("((a #b00101010))").parsed_output);
      CHECK(
        *response_42.get_if_valid() ==
        smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
          smt_identifier_termt{"a", smt_bit_vector_sortt{8}},
          smt_bit_vector_constant_termt{42, 8}}}});
    }
  }
  SECTION("Multiple valuation pairs.")
  {
    const response_or_errort<smt_responset> two_pair_response =
      validate_smt_response(*smt2irep("((a true) (b false))").parsed_output);
    CHECK(
      *two_pair_response.get_if_valid() ==
      smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
                                 smt_identifier_termt{"a", smt_bool_sortt{}},
                                 smt_bool_literal_termt{true}},
                               smt_get_value_responset::valuation_pairt{
                                 smt_identifier_termt{"b", smt_bool_sortt{}},
                                 smt_bool_literal_termt{false}}}});
  }
  SECTION("Invalid terms.")
  {
    const response_or_errort<smt_responset> empty_value_response =
      validate_smt_response(*smt2irep("((a ())))").parsed_output);
    CHECK(
      *empty_value_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\"."});
    const response_or_errort<smt_responset> pair_value_response =
      validate_smt_response(*smt2irep("((a (#xF00D #xBAD))))").parsed_output);
    CHECK(
      *pair_value_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\n"
                               "0: #xF00D\n"
                               "1: #xBAD\"."});
    const response_or_errort<smt_responset> two_pair_value_response =
      validate_smt_response(
        *smt2irep("((a (#xF00D #xBAD)) (b (#xDEAD #xFA11)))").parsed_output);
    CHECK(
      *two_pair_value_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\n"
                               "0: #xF00D\n"
                               "1: #xBAD\".",
                               "Unrecognised SMT term - \"\n"
                               "0: #xDEAD\n"
                               "1: #xFA11\"."});
    const response_or_errort<smt_responset> empty_descriptor_response =
      validate_smt_response(*smt2irep("((() true))").parsed_output);
    CHECK(
      *empty_descriptor_response.get_if_error() ==
      std::vector<std::string>{"Expected identifier, found - \"\"."});
    const response_or_errort<smt_responset> empty_pair =
      validate_smt_response(*smt2irep("((() ())))").parsed_output);
    CHECK(
      *empty_pair.get_if_error() ==
      std::vector<std::string>{"Expected identifier, found - \"\".",
                               "Unrecognised SMT term - \"\"."});
  }
}
