// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_commands.h>
#include <solvers/smt2_incremental/smt_logics.h>
#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/smt2_incremental/smt_to_string.h>

#include <util/mp_arith.h>

TEST_CASE("Test smt_sortt to string conversion", "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bool_sortt{}) == "Bool");
  CHECK(smt_to_string(smt_bit_vector_sortt{16}) == "(_ BitVec 16)");
}

TEST_CASE("Test smt_not_termt to string conversion", "[core][smt2_incremental]")
{
  CHECK(
    smt_to_string(smt_not_termt{
      smt_identifier_termt{"foo", smt_bool_sortt{}}}) == "(not |foo|)");
}

TEST_CASE(
  "Test smt_bit_vector_constant_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bit_vector_constant_termt{0, 8}) == "(_ bv0 8)");
}

TEST_CASE(
  "Test smt_bool_literal_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bool_literal_termt{true}) == "true");
  CHECK(smt_to_string(smt_bool_literal_termt{false}) == "false");
}

TEST_CASE(
  "Test smt_function_application_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_string(smt_function_application_termt{
      smt_identifier_termt{"=", smt_bool_sortt{}},
      {smt_identifier_termt{"foo", smt_bit_vector_sortt{32}},
       {smt_identifier_termt{"bar", smt_bit_vector_sortt{32}}}}}) ==
    "(|=| |foo| |bar|)");
}

TEST_CASE(
  "Test smt_check_sat_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_check_sat_commandt{}) == "(check-sat)");
}

TEST_CASE(
  "Test smt_exit_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_exit_commandt{}) == "(exit)");
}

TEST_CASE(
  "Test smt_push_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_push_commandt{1}) == "(push 1)");
  CHECK(smt_to_string(smt_push_commandt{2}) == "(push 2)");
}

TEST_CASE(
  "Test smt_pop_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_pop_commandt{1}) == "(pop 1)");
  CHECK(smt_to_string(smt_pop_commandt{2}) == "(pop 2)");
}

TEST_CASE(
  "Test smt_assert_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_string(smt_assert_commandt{smt_bool_literal_termt{true}}) ==
    "(assert true)");
}

TEST_CASE(
  "Test smt_declare_function_commandt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_string(smt_declare_function_commandt{
      smt_identifier_termt{"f", smt_bit_vector_sortt{31}},
      {smt_bit_vector_sortt{32}, smt_bit_vector_sortt{33}}}) ==
    "(declare-fun |f| ((_ BitVec 32) (_ BitVec 33)) (_ BitVec 31))");
}

TEST_CASE(
  "Test smt_define_function_commandt to string conversion",
  "[core][smt2_incremental]")
{
  const auto g = smt_identifier_termt{"g", smt_bit_vector_sortt{32}};
  const auto h = smt_identifier_termt{"h", smt_bit_vector_sortt{32}};

  CHECK(
    smt_to_string(smt_define_function_commandt{
      "f",
      {g, h},
      smt_function_application_termt{
        smt_identifier_termt{"=", smt_bool_sortt{}}, {g, h}}}) ==
    "(define-fun |f| ((|g| (_ BitVec 32)) (|h| (_ BitVec 32))) Bool (|=| |g| "
    "|h|))");
}

TEST_CASE(
  "Test smt_set_option_commandt to string conversion",
  "[core][smt2_incremental]")
{
  const auto with_models = smt_option_produce_modelst{true};
  const auto no_models = smt_option_produce_modelst{false};
  CHECK(smt_to_string(with_models) == ":produce-models true");
  CHECK(smt_to_string(no_models) == ":produce-models false");
  CHECK(
    smt_to_string(smt_set_option_commandt{with_models}) ==
    "(set-option :produce-models true)");
  CHECK(
    smt_to_string(smt_set_option_commandt{no_models}) ==
    "(set-option :produce-models false)");
}

TEST_CASE(
  "Test smt_set_logic_commandt to string conversion",
  "[core][smt2_incremental]")
{
  const smt_logic_quantifier_free_bit_vectorst qf_bv;
  CHECK(smt_to_string(qf_bv) == "QF_BV");
  CHECK(smt_to_string(smt_set_logic_commandt{qf_bv}) == "(set-logic QF_BV)");
}
