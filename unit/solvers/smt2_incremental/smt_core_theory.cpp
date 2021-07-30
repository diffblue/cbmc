// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/mp_arith.h>

TEST_CASE("SMT core theory \"not\".", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt operand{true};
  const auto not_term = smt_core_theoryt::make_not(operand);

  CHECK(not_term.get_sort() == smt_bool_sortt{});
  CHECK(
    not_term.function_identifier() ==
    smt_identifier_termt{"not", smt_bool_sortt{}});
  REQUIRE(not_term.arguments().size() == 1);
  REQUIRE(not_term.arguments()[0].get() == operand);
  cbmc_invariants_should_throwt invariants_throw;
  CHECK_THROWS(smt_core_theoryt::make_not(smt_bit_vector_constant_termt{0, 1}));
}

TEST_CASE("SMT core theory implies.", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt true_term{true};
  const smt_bool_literal_termt false_term{false};
  const auto implies = smt_core_theoryt::implies(true_term, false_term);
  CHECK(implies.get_sort() == smt_bool_sortt{});
  CHECK(
    implies.function_identifier() ==
    smt_identifier_termt{"=>", smt_bool_sortt{}});
  REQUIRE(implies.arguments().size() == 2);
  CHECK(implies.arguments()[0].get() == true_term);
  CHECK(implies.arguments()[1].get() == false_term);
  cbmc_invariants_should_throwt invariants_throw;
  const smt_bit_vector_constant_termt two{2, 8};
  CHECK_THROWS(smt_core_theoryt::implies(two, false_term));
  CHECK_THROWS(smt_core_theoryt::implies(true_term, two));
}

TEST_CASE("SMT core theory \"and\".", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt true_term{true};
  const smt_bool_literal_termt false_term{false};
  const auto implies = smt_core_theoryt::make_and(true_term, false_term);
  CHECK(implies.get_sort() == smt_bool_sortt{});
  CHECK(
    implies.function_identifier() ==
    smt_identifier_termt{"and", smt_bool_sortt{}});
  REQUIRE(implies.arguments().size() == 2);
  CHECK(implies.arguments()[0].get() == true_term);
  CHECK(implies.arguments()[1].get() == false_term);
  cbmc_invariants_should_throwt invariants_throw;
  const smt_bit_vector_constant_termt two{2, 8};
  CHECK_THROWS(smt_core_theoryt::make_and(two, false_term));
  CHECK_THROWS(smt_core_theoryt::make_and(true_term, two));
}

TEST_CASE("SMT core theory \"or\".", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt true_term{true};
  const smt_bool_literal_termt false_term{false};
  const auto implies = smt_core_theoryt::make_or(true_term, false_term);
  CHECK(implies.get_sort() == smt_bool_sortt{});
  CHECK(
    implies.function_identifier() ==
    smt_identifier_termt{"or", smt_bool_sortt{}});
  REQUIRE(implies.arguments().size() == 2);
  CHECK(implies.arguments()[0].get() == true_term);
  CHECK(implies.arguments()[1].get() == false_term);
  cbmc_invariants_should_throwt invariants_throw;
  const smt_bit_vector_constant_termt two{2, 8};
  CHECK_THROWS(smt_core_theoryt::make_or(two, false_term));
  CHECK_THROWS(smt_core_theoryt::make_or(true_term, two));
}

TEST_CASE("SMT core theory \"xor\".", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt true_term{true};
  const smt_bool_literal_termt false_term{false};
  const auto implies = smt_core_theoryt::make_xor(true_term, false_term);
  CHECK(implies.get_sort() == smt_bool_sortt{});
  CHECK(
    implies.function_identifier() ==
    smt_identifier_termt{"xor", smt_bool_sortt{}});
  REQUIRE(implies.arguments().size() == 2);
  CHECK(implies.arguments()[0].get() == true_term);
  CHECK(implies.arguments()[1].get() == false_term);
  cbmc_invariants_should_throwt invariants_throw;
  const smt_bit_vector_constant_termt two{2, 8};
  CHECK_THROWS(smt_core_theoryt::make_xor(two, false_term));
  CHECK_THROWS(smt_core_theoryt::make_xor(true_term, two));
}

TEST_CASE("SMT core theory \"=\".", "[core][smt2_incremental]")
{
  SECTION("Bool sorted term comparison")
  {
    const smt_bool_literal_termt true_term{true};
    const smt_bool_literal_termt false_term{false};
    const auto bool_comparison = smt_core_theoryt::equal(true_term, false_term);
    CHECK(bool_comparison.get_sort() == smt_bool_sortt{});
    CHECK(
      bool_comparison.function_identifier() ==
      smt_identifier_termt{"=", smt_bool_sortt{}});
    REQUIRE(bool_comparison.arguments().size() == 2);
    REQUIRE(bool_comparison.arguments()[0].get() == true_term);
    REQUIRE(bool_comparison.arguments()[1].get() == false_term);
  }

  SECTION("Bit vector sorted term comparison")
  {
    const smt_bit_vector_constant_termt two{2, 8};
    const smt_bit_vector_constant_termt three{3, 8};
    const auto bit_vector_comparison = smt_core_theoryt::equal(two, three);
    CHECK(bit_vector_comparison.get_sort() == smt_bool_sortt{});
    CHECK(
      bit_vector_comparison.function_identifier() ==
      smt_identifier_termt{"=", smt_bool_sortt{}});
    REQUIRE(bit_vector_comparison.arguments().size() == 2);
    REQUIRE(bit_vector_comparison.arguments()[0].get() == two);
    REQUIRE(bit_vector_comparison.arguments()[1].get() == three);
  }

  SECTION("Mismatch sort invariant")
  {
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_core_theoryt::equal(
      smt_bit_vector_constant_termt{2, 8},
      smt_bit_vector_constant_termt{2, 16}));
    CHECK_THROWS(smt_core_theoryt::equal(
      smt_bit_vector_constant_termt{2, 8}, smt_bool_literal_termt{true}));
  }
}

TEST_CASE("SMT core theory \"distinct\".", "[core][smt2_incremental]")
{
  SECTION("Bool sorted term comparison")
  {
    const smt_bool_literal_termt true_term{true};
    const smt_bool_literal_termt false_term{false};
    const auto bool_comparison =
      smt_core_theoryt::distinct(true_term, false_term);
    CHECK(bool_comparison.get_sort() == smt_bool_sortt{});
    CHECK(
      bool_comparison.function_identifier() ==
      smt_identifier_termt{"distinct", smt_bool_sortt{}});
    REQUIRE(bool_comparison.arguments().size() == 2);
    REQUIRE(bool_comparison.arguments()[0].get() == true_term);
    REQUIRE(bool_comparison.arguments()[1].get() == false_term);
  }

  SECTION("Bit vector sorted term comparison")
  {
    const smt_bit_vector_constant_termt two{2, 8};
    const smt_bit_vector_constant_termt three{3, 8};
    const auto bit_vector_comparison = smt_core_theoryt::distinct(two, three);
    CHECK(bit_vector_comparison.get_sort() == smt_bool_sortt{});
    CHECK(
      bit_vector_comparison.function_identifier() ==
      smt_identifier_termt{"distinct", smt_bool_sortt{}});
    REQUIRE(bit_vector_comparison.arguments().size() == 2);
    REQUIRE(bit_vector_comparison.arguments()[0].get() == two);
    REQUIRE(bit_vector_comparison.arguments()[1].get() == three);
  }

  SECTION("Mismatch sort invariant")
  {
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_core_theoryt::distinct(
      smt_bit_vector_constant_termt{2, 8},
      smt_bit_vector_constant_termt{2, 16}));
    CHECK_THROWS(smt_core_theoryt::distinct(
      smt_bit_vector_constant_termt{2, 8}, smt_bool_literal_termt{true}));
  }
}

TEST_CASE("SMT core theory if then else.", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt false_term{false};
  const smt_bit_vector_constant_termt two{2, 8};
  const smt_bit_vector_constant_termt three{2, 8};
  const auto if_then_else =
    smt_core_theoryt::if_then_else(false_term, two, three);
  CHECK(if_then_else.get_sort() == smt_bit_vector_sortt{8});
  CHECK(
    if_then_else.function_identifier() ==
    smt_identifier_termt{"ite", smt_bit_vector_sortt{8}});
  REQUIRE(if_then_else.arguments().size() == 3);
  CHECK(if_then_else.arguments()[0].get() == false_term);
  CHECK(if_then_else.arguments()[1].get() == two);
  CHECK(if_then_else.arguments()[2].get() == three);
  cbmc_invariants_should_throwt invariants_throw;
  CHECK_THROWS(smt_core_theoryt::if_then_else(two, two, three));
  CHECK_THROWS(smt_core_theoryt::if_then_else(false_term, false_term, three));
}
