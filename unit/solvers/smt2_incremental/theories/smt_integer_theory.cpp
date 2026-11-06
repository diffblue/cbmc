// Author: Michael Tautschnig

#include <util/mp_arith.h> // IWYU pragma: keep

#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/theories/smt_integer_theory.h>
#include <testing-utils/use_catch.h>

TEST_CASE("SMT integer arithmetic operators", "[core][smt2_incremental]")
{
  const smt_int_constant_termt three{3}, four{4};

  SECTION("Addition")
  {
    const auto sum = smt_integer_theoryt::add(three, four);
    REQUIRE(
      sum.function_identifier() == smt_identifier_termt("+", smt_int_sortt{}));
    REQUIRE(sum.get_sort() == smt_int_sortt{});
    REQUIRE(sum.arguments().size() == 2);
    REQUIRE(sum.arguments()[0].get() == three);
    REQUIRE(sum.arguments()[1].get() == four);
  }
  SECTION("Subtraction")
  {
    const auto difference = smt_integer_theoryt::sub(three, four);
    REQUIRE(
      difference.function_identifier() ==
      smt_identifier_termt("-", smt_int_sortt{}));
    REQUIRE(difference.get_sort() == smt_int_sortt{});
  }
  SECTION("Multiplication")
  {
    const auto product = smt_integer_theoryt::mul(three, four);
    REQUIRE(
      product.function_identifier() ==
      smt_identifier_termt("*", smt_int_sortt{}));
    REQUIRE(product.get_sort() == smt_int_sortt{});
  }
  SECTION("Division (SMT-LIB Euclidean div)")
  {
    const auto quotient = smt_integer_theoryt::divide(three, four);
    REQUIRE(
      quotient.function_identifier() ==
      smt_identifier_termt("div", smt_int_sortt{}));
    REQUIRE(quotient.get_sort() == smt_int_sortt{});
  }
  SECTION("Modulo (SMT-LIB Euclidean mod)")
  {
    const auto remainder = smt_integer_theoryt::mod(three, four);
    REQUIRE(
      remainder.function_identifier() ==
      smt_identifier_termt("mod", smt_int_sortt{}));
    REQUIRE(remainder.get_sort() == smt_int_sortt{});
  }
  SECTION("Unary minus")
  {
    const auto negated = smt_integer_theoryt::negate(three);
    REQUIRE(
      negated.function_identifier() ==
      smt_identifier_termt("-", smt_int_sortt{}));
    REQUIRE(negated.get_sort() == smt_int_sortt{});
    REQUIRE(negated.arguments().size() == 1);
    REQUIRE(negated.arguments()[0].get() == three);
  }
  SECTION("Operands must be integer sorted")
  {
    const smt_bool_literal_termt false_term{false};
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_integer_theoryt::add(three, false_term));
    CHECK_THROWS(smt_integer_theoryt::add(false_term, three));
    CHECK_THROWS(smt_integer_theoryt::sub(three, false_term));
    CHECK_THROWS(smt_integer_theoryt::mul(three, false_term));
    CHECK_THROWS(smt_integer_theoryt::divide(three, false_term));
    CHECK_THROWS(smt_integer_theoryt::mod(three, false_term));
    CHECK_THROWS(smt_integer_theoryt::negate(false_term));
  }
}

TEST_CASE("SMT integer relational operators", "[core][smt2_incremental]")
{
  const smt_int_constant_termt three{3}, four{4};

  SECTION("Comparisons return Bool")
  {
    const auto less = smt_integer_theoryt::less_than(three, four);
    REQUIRE(
      less.function_identifier() ==
      smt_identifier_termt("<", smt_bool_sortt{}));
    REQUIRE(less.get_sort() == smt_bool_sortt{});

    REQUIRE(
      smt_integer_theoryt::less_than_or_equal(three, four)
        .function_identifier() == smt_identifier_termt("<=", smt_bool_sortt{}));
    REQUIRE(
      smt_integer_theoryt::greater_than(three, four).function_identifier() ==
      smt_identifier_termt(">", smt_bool_sortt{}));
    REQUIRE(
      smt_integer_theoryt::greater_than_or_equal(three, four)
        .function_identifier() == smt_identifier_termt(">=", smt_bool_sortt{}));
  }
  SECTION("Operands must be integer sorted")
  {
    const smt_bool_literal_termt false_term{false};
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_integer_theoryt::less_than(three, false_term));
    CHECK_THROWS(smt_integer_theoryt::greater_than_or_equal(false_term, three));
  }
}
