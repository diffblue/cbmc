// Author: Diffblue Ltd.

#include <util/mp_arith.h>

#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_commands.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_logics.h>
#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>
#include <testing-utils/use_catch.h>

#include <tuple>

TEST_CASE("Test smt_indext to string conversion", "[core][smt2_incremental]")
{
  std::string input_term;
  std::string expected_term;
  using rowt = std::pair<std::string, std::string>;

  std::tie(input_term, expected_term) = GENERATE(
    rowt{"green", "green"},
    rowt{"abc76473*^&", "abc76473*^&"},
    rowt{"my name is", "|my name is|"},
    // The following are example symbols from the SMTLIB spec.
    rowt{"+", "+"},
    rowt{"**", "**"},
    rowt{".kkk", ".kkk"},
    rowt{"-32", "-32"},
    rowt{" \" can occur too", "| \" can occur too|"});

  SECTION("check that index identifiers are constructed accordingly")
  {
    CHECK(smt_to_smt2_string(smt_symbol_indext{input_term}) == expected_term);
  }
  CHECK(smt_to_smt2_string(smt_numeral_indext{42}) == "42");
}

TEST_CASE("Test smt_sortt to string conversion", "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_bool_sortt{}) == "Bool");
  CHECK(smt_to_smt2_string(smt_bit_vector_sortt{16}) == "(_ BitVec 16)");
}

TEST_CASE(
  "Test smt_bit_vector_constant_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_bit_vector_constant_termt{0, 8}) == "(_ bv0 8)");
}

TEST_CASE(
  "Test smt_bit_vector extract to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_smt2_string(smt_bit_vector_theoryt::extract(7, 3)(
      smt_bit_vector_constant_termt{0, 8})) == "((_ extract 7 3) (_ bv0 8))");
}

TEST_CASE(
  "Test smt_bool_literal_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_bool_literal_termt{true}) == "true");
  CHECK(smt_to_smt2_string(smt_bool_literal_termt{false}) == "false");
}

TEST_CASE(
  "Test smt_identifier_termt to string conversion",
  "[core][smt2_incremental]")
{
  std::string input_term;
  std::string expected_term;
  using rowt = std::pair<std::string, std::string>;

  std::tie(input_term, expected_term) = GENERATE(
    rowt{"abc", "abc"},
    rowt{"\\", "|&92;|"},
    rowt{"green", "green"},
    rowt{"abc76473*^&", "abc76473*^&"},
    rowt{"my name is", "|my name is|"},
    // The following are example symbols from the SMTLIB spec.
    rowt{"+", "+"},
    rowt{"**", "**"},
    rowt{".kkk", ".kkk"},
    rowt{"-32", "-32"},
    rowt{" \" can occur too", "| \" can occur too|"});

  SECTION("Simple identifiers")
  {
    CHECK(
      smt_to_smt2_string(smt_identifier_termt{input_term, smt_bool_sortt{}}) ==
      expected_term);
  }

  SECTION("Indexed identifier")
  {
    CHECK(
      smt_to_smt2_string(smt_identifier_termt{
        "foo",
        smt_bool_sortt{},
        {smt_symbol_indext{"bar"}, smt_numeral_indext{42}}}) ==
      "(_ foo bar 42)");
  }
}

TEST_CASE(
  "Test smt_function_application_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_smt2_string(smt_core_theoryt::equal(
      smt_identifier_termt{"foo", smt_bit_vector_sortt{32}},
      smt_identifier_termt{"bar", smt_bit_vector_sortt{32}})) == "(= foo bar)");
}

TEST_CASE(
  "Test smt_check_sat_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_check_sat_commandt{}) == "(check-sat)");
}

TEST_CASE(
  "Test smt_exit_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_exit_commandt{}) == "(exit)");
}

TEST_CASE(
  "Test smt_get_value_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_smt2_string(smt_get_value_commandt{
      smt_identifier_termt{"foo", smt_bool_sortt{}}}) == "(get-value (foo))");
}

TEST_CASE(
  "Test smt_push_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_push_commandt{1}) == "(push 1)");
  CHECK(smt_to_smt2_string(smt_push_commandt{2}) == "(push 2)");
}

TEST_CASE(
  "Test smt_pop_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_smt2_string(smt_pop_commandt{1}) == "(pop 1)");
  CHECK(smt_to_smt2_string(smt_pop_commandt{2}) == "(pop 2)");
}

TEST_CASE(
  "Test smt_assert_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_smt2_string(smt_assert_commandt{smt_bool_literal_termt{true}}) ==
    "(assert true)");
}

TEST_CASE(
  "Test smt_declare_function_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_smt2_string(smt_declare_function_commandt{
      smt_identifier_termt{"f", smt_bit_vector_sortt{31}},
      {smt_bit_vector_sortt{32}, smt_bit_vector_sortt{33}}}) ==
    "(declare-fun f ((_ BitVec 32) (_ BitVec 33)) (_ BitVec 31))");
}

TEST_CASE(
  "Test smt_define_function_commandt to string conversion",
  "[core][smt2_incremental]")
{
  const auto g = smt_identifier_termt{"g", smt_bit_vector_sortt{32}};
  const auto h = smt_identifier_termt{"h", smt_bit_vector_sortt{32}};

  CHECK(
    smt_to_smt2_string(smt_define_function_commandt{
      "f", {g, h}, smt_core_theoryt::equal(g, h)}) ==
    "(define-fun f ((g (_ BitVec 32)) (h (_ BitVec 32))) Bool (= g h))");
}

TEST_CASE(
  "Test smt_set_option_commandt to string conversion",
  "[core][smt2_incremental]")
{
  const auto with_models = smt_option_produce_modelst{true};
  const auto no_models = smt_option_produce_modelst{false};
  CHECK(smt_to_smt2_string(with_models) == ":produce-models true");
  CHECK(smt_to_smt2_string(no_models) == ":produce-models false");
  CHECK(
    smt_to_smt2_string(smt_set_option_commandt{with_models}) ==
    "(set-option :produce-models true)");
  CHECK(
    smt_to_smt2_string(smt_set_option_commandt{no_models}) ==
    "(set-option :produce-models false)");
}

TEST_CASE(
  "Test smt_set_logic_commandt to string conversion",
  "[core][smt2_incremental]")
{
  const auto qf_uf = smt_logic_quantifier_free_uninterpreted_functionst{};
  CHECK(smt_to_smt2_string(qf_uf) == "QF_UF");
  const auto qf_bv = smt_logic_quantifier_free_bit_vectorst{};
  CHECK(smt_to_smt2_string(qf_bv) == "QF_BV");
  const auto qf_ufbv =
    smt_logic_quantifier_free_uninterpreted_functions_bit_vectorst{};
  CHECK(smt_to_smt2_string(qf_ufbv) == "QF_UFBV");
  const auto qf_abv = smt_logic_quantifier_free_bit_vectors_arrayst{};
  CHECK(smt_to_smt2_string(qf_abv) == "QF_ABV");
  const auto qf_aufbv =
    smt_logic_quantifier_free_uninterpreted_functions_bit_vectors_arrayst{};
  CHECK(smt_to_smt2_string(qf_aufbv) == "QF_AUFBV");
  CHECK(smt_to_smt2_string(smt_logic_allt{}) == "ALL");
  CHECK(
    smt_to_smt2_string(smt_set_logic_commandt{qf_bv}) == "(set-logic QF_BV)");
}
