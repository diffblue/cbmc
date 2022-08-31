// Author: Diffblue Ltd.

#include <util/mp_arith.h>

#include <solvers/smt2_incremental/smt_array_theory.h>
#include <solvers/smt2_incremental/smt_response_validation.h>
#include <testing-utils/smt2irep.h>
#include <testing-utils/use_catch.h>

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
    *validate_smt_response(*smt2irep("sat").parsed_output, {}).get_if_valid() ==
    smt_check_sat_responset{smt_sat_responset{}});
  CHECK(
    *validate_smt_response(*smt2irep("unsat").parsed_output, {})
       .get_if_valid() == smt_check_sat_responset{smt_unsat_responset{}});
  CHECK(
    *validate_smt_response(*smt2irep("unknown").parsed_output, {})
       .get_if_valid() == smt_check_sat_responset{smt_unknown_responset{}});
}

TEST_CASE("Validation of SMT success response", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(*smt2irep("success").parsed_output, {})
       .get_if_valid() == smt_success_responset{});
}

TEST_CASE("Validation of SMT unsupported response", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(*smt2irep("unsupported").parsed_output, {})
       .get_if_valid() == smt_unsupported_responset{});
}

TEST_CASE(
  "Error handling of SMT response validation",
  "[core][smt2_incremental]")
{
  SECTION("Parse tree produced is not a valid SMT-LIB version 2.6 response")
  {
    const response_or_errort<smt_responset> validation_response =
      validate_smt_response(*smt2irep("foobar").parsed_output, {});
    CHECK(
      *validation_response.get_if_error() ==
      std::vector<std::string>{"Invalid SMT response \"foobar\""});
    CHECK(
      *validate_smt_response(*smt2irep("()").parsed_output, {})
         .get_if_error() ==
      std::vector<std::string>{"Invalid SMT response \"\""});
  }
}

TEST_CASE("Validation of SMT error response", "[core][smt2_incremental]")
{
  CHECK(
    *validate_smt_response(
       *smt2irep("(error \"Test error message.\")").parsed_output, {})
       .get_if_valid() == smt_error_responset{"Test error message."});
  CHECK(
    *validate_smt_response(*smt2irep("(error)").parsed_output, {})
       .get_if_error() ==
    std::vector<std::string>{"Error response is missing the error message."});
  CHECK(
    *validate_smt_response(
       *smt2irep("(error \"Test error message1.\" \"Test error message2.\")")
          .parsed_output,
       {})
       .get_if_error() ==
    std::vector<std::string>{"Error response has multiple error messages - \"\n"
                             "0: error\n"
                             "1: Test error message1.\n"
                             "2: Test error message2.\"."});
}

TEST_CASE("smt get-value response validation", "[core][smt2_incremental]")
{
  const auto table_with_identifiers =
    [](const std::vector<std::pair<std::string, smt_sortt>> &identifiers) {
      std::unordered_map<irep_idt, smt_identifier_termt> table;
      for(auto &identifier_pair : identifiers)
      {
        auto &identifier = identifier_pair.first;
        auto &sort = identifier_pair.second;
        table.insert({identifier, smt_identifier_termt{identifier, sort}});
      }
      return table;
    };
  SECTION("Boolean sorted values.")
  {
    const auto identifier_table =
      table_with_identifiers({{"a", smt_bool_sortt{}}});
    const response_or_errort<smt_responset> true_response =
      validate_smt_response(
        *smt2irep("((a true))").parsed_output, identifier_table);
    CHECK(
      *true_response.get_if_valid() ==
      smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
        smt_identifier_termt{"a", smt_bool_sortt{}},
        smt_bool_literal_termt{true}}}});
    const response_or_errort<smt_responset> false_response =
      validate_smt_response(
        *smt2irep("((a false))").parsed_output, identifier_table);
    CHECK(
      *false_response.get_if_valid() ==
      smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
        smt_identifier_termt{"a", smt_bool_sortt{}},
        smt_bool_literal_termt{false}}}});
  }
  SECTION("Bit vector sorted values.")
  {
    const auto identifier_table =
      table_with_identifiers({{"a", smt_bit_vector_sortt{8}}});
    SECTION("Hex value")
    {
      const response_or_errort<smt_responset> response_255 =
        validate_smt_response(
          *smt2irep("((a #xff))").parsed_output, identifier_table);
      CHECK(
        *response_255.get_if_valid() ==
        smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
          smt_identifier_termt{"a", smt_bit_vector_sortt{8}},
          smt_bit_vector_constant_termt{255, 8}}}});
    }
    SECTION("Binary value")
    {
      const response_or_errort<smt_responset> response_42 =
        validate_smt_response(
          *smt2irep("((a #b00101010))").parsed_output, identifier_table);
      CHECK(
        *response_42.get_if_valid() ==
        smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
          smt_identifier_termt{"a", smt_bit_vector_sortt{8}},
          smt_bit_vector_constant_termt{42, 8}}}});
    }
    SECTION("Array values")
    {
      // Construction of select part of response
      const smt_bit_vector_constant_termt index_term(
        0xA, smt_bit_vector_sortt(32));
      const smt_sortt value_sort(smt_bit_vector_sortt(32));
      const smt_identifier_termt array_term(
        "b", smt_array_sortt(index_term.get_sort(), value_sort));
      const smt_function_application_termt select =
        smt_array_theoryt::select(array_term, index_term);
      // Identifier table needs to contain identifier of array
      const auto identifier_table = table_with_identifiers(
        {{"b",
          smt_array_sortt{
            smt_bit_vector_sortt{32}, smt_bit_vector_sortt{32}}}});

      SECTION("Valid application of smt_array_theoryt::select")
      {
        const response_or_errort<smt_responset> response_get_select =
          validate_smt_response(
            *smt2irep("(((select |b| (_ bv10 32)) #x0000002a))").parsed_output,
            identifier_table);
        CHECK(
          *response_get_select.get_if_valid() ==
          smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
            select, smt_bit_vector_constant_termt{0x2A, 32}}}});
      }
      SECTION("Invalid due to selecting from non-array")
      {
        const response_or_errort<smt_responset> response_get_select =
          validate_smt_response(
            *smt2irep("(((select (_ bv10 32) (_ bv10 32)) #x0000002a))")
               .parsed_output,
            identifier_table);
        CHECK(
          *response_get_select.get_if_error() ==
          std::vector<std::string>{
            "\"select\" may only select from an array."});
      }
      SECTION("Invalid due to selecting invalid index sort")
      {
        const response_or_errort<smt_responset> response_get_select =
          validate_smt_response(
            *smt2irep("(((select |b| (_ bv10 16)) #x0000002a))").parsed_output,
            identifier_table);
        CHECK(
          *response_get_select.get_if_error() ==
          std::vector<std::string>{
            "Sort of arrays index must match the sort of the index supplied."});
      }
    }
    SECTION("Descriptors which are bit vector constants")
    {
      const response_or_errort<smt_responset> response_descriptor =
        validate_smt_response(
          *smt2irep("(((_ bv255 8) #x2A))").parsed_output, {});
      CHECK(
        *response_descriptor.get_if_valid() ==
        smt_get_value_responset{{smt_get_value_responset::valuation_pairt{
          smt_bit_vector_constant_termt{255, 8},
          smt_bit_vector_constant_termt{42, 8}}}});
      SECTION("Invalid bit vector constants")
      {
        SECTION("Value too large for width")
        {
          const response_or_errort<smt_responset> pair_value_response =
            validate_smt_response(
              *smt2irep("(((_ bv256 8) #xff))").parsed_output, {});
          CHECK(
            *pair_value_response.get_if_error() ==
            std::vector<std::string>{"Unrecognised SMT term - \"\n"
                                     "0: _\n"
                                     "1: bv256\n"
                                     "2: 8\"."});
        }
        SECTION("Value missing bv prefix.")
        {
          const response_or_errort<smt_responset> pair_value_response =
            validate_smt_response(
              *smt2irep("(((_ 42 8) #xff))").parsed_output, {});
          CHECK(
            *pair_value_response.get_if_error() ==
            std::vector<std::string>{"Unrecognised SMT term - \"\n"
                                     "0: _\n"
                                     "1: 42\n"
                                     "2: 8\"."});
        }
        SECTION("Hex value.")
        {
          const response_or_errort<smt_responset> pair_value_response =
            validate_smt_response(
              *smt2irep("(((_ bv2A 8) #xff))").parsed_output, {});
          CHECK(
            *pair_value_response.get_if_error() ==
            std::vector<std::string>{"Unrecognised SMT term - \"\n"
                                     "0: _\n"
                                     "1: bv2A\n"
                                     "2: 8\"."});
        }
        SECTION("Zero width.")
        {
          const response_or_errort<smt_responset> pair_value_response =
            validate_smt_response(
              *smt2irep("(((_ bv0 0) #xff))").parsed_output, {});
          CHECK(
            *pair_value_response.get_if_error() ==
            std::vector<std::string>{"Unrecognised SMT term - \"\n"
                                     "0: _\n"
                                     "1: bv0\n"
                                     "2: 0\"."});
        }
      }
    }
  }
  SECTION("Multiple valuation pairs.")
  {
    const auto identifier_table = table_with_identifiers(
      {{"a", smt_bool_sortt{}}, {"b", smt_bool_sortt{}}});
    const response_or_errort<smt_responset> two_pair_response =
      validate_smt_response(
        *smt2irep("((a true) (b false))").parsed_output, identifier_table);
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
    const auto identifier_table = table_with_identifiers(
      {{"a", smt_bit_vector_sortt{16}}, {"b", smt_bit_vector_sortt{16}}});
    const response_or_errort<smt_responset> empty_value_response =
      validate_smt_response(
        *smt2irep("((a ())))").parsed_output, identifier_table);
    CHECK(
      *empty_value_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\"."});
    const response_or_errort<smt_responset> unknown_identifier_response =
      validate_smt_response(
        *smt2irep("((foo bar)))").parsed_output, identifier_table);
    CHECK(
      *unknown_identifier_response.get_if_error() ==
      std::vector<std::string>{
        "Unrecognised SMT term - \"foo\".",
        "Unrecognised SMT term - \"bar\"."});
    const response_or_errort<smt_responset> pair_value_response =
      validate_smt_response(
        *smt2irep("((a (#xF00D #xBAD))))").parsed_output, identifier_table);
    CHECK(
      *pair_value_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\n"
                               "0: #xF00D\n"
                               "1: #xBAD\"."});
    const response_or_errort<smt_responset> two_pair_value_response =
      validate_smt_response(
        *smt2irep("((a (#xF00D #xBAD)) (b (#xDEAD #xFA11)))").parsed_output,
        identifier_table);
    CHECK(
      *two_pair_value_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\n"
                               "0: #xF00D\n"
                               "1: #xBAD\".",
                               "Unrecognised SMT term - \"\n"
                               "0: #xDEAD\n"
                               "1: #xFA11\"."});
    const response_or_errort<smt_responset> empty_descriptor_response =
      validate_smt_response(*smt2irep("((() true))").parsed_output, {});
    CHECK(
      *empty_descriptor_response.get_if_error() ==
      std::vector<std::string>{"Unrecognised SMT term - \"\"."});
    const response_or_errort<smt_responset> empty_pair =
      validate_smt_response(*smt2irep("((() ())))").parsed_output, {});
    CHECK(
      *empty_pair.get_if_error() ==
      std::vector<std::string>{
        "Unrecognised SMT term - \"\".", "Unrecognised SMT term - \"\"."});
  }
}
