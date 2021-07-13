// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_terms.h>

#include <util/mp_arith.h>

#include <type_traits>

TEST_CASE("Test smt_termt.pretty is accessible.", "[core][smt2_incremental]")
{
  const smt_termt bool_term{smt_bool_literal_termt{true}};
  REQUIRE(
    bool_term.pretty(0, 0) ==
    "smt_bool_literal_term\n"
    "  * type: smt_bool_sort\n"
    "  * value: 1");
}

TEST_CASE(
  "Test smt_bool_literal_termt has bool sort.",
  "[core][smt2_incremental]")
{
  REQUIRE(smt_bool_literal_termt{true}.get_sort() == smt_bool_sortt{});
}

TEST_CASE(
  "Test smt_bool_literal_termt value getter.",
  "[core][smt2_incremental]")
{
  REQUIRE(smt_bool_literal_termt{true}.value());
  REQUIRE_FALSE(smt_bool_literal_termt{false}.value());
}

TEST_CASE("smt_not_termt sort.", "[core][smt2_incremental]")
{
  REQUIRE(
    smt_not_termt{smt_bool_literal_termt{true}}.get_sort() == smt_bool_sortt{});
}

TEST_CASE("smt_not_termt operand getter.", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt bool_term{true};
  const smt_not_termt not_term{bool_term};
  REQUIRE(not_term.operand() == bool_term);
}

TEST_CASE("smt_identifier_termt construction", "[core][smt2_incremental]")
{
  cbmc_invariants_should_throwt invariants_throw;
  CHECK_NOTHROW(smt_identifier_termt{"foo bar", smt_bool_sortt{}});
  CHECK_THROWS(smt_identifier_termt{"|foo bar|", smt_bool_sortt{}});
  CHECK_THROWS(smt_identifier_termt{"foo\\ bar", smt_bool_sortt{}});
}

TEST_CASE("smt_identifier_termt getters.", "[core][smt2_incremental]")
{
  const smt_identifier_termt identifier{"foo", smt_bool_sortt{}};
  CHECK(identifier.identifier() == "foo");
  CHECK(identifier.get_sort() == smt_bool_sortt{});
}

TEST_CASE("smt_bit_vector_constant_termt getters.", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt bit_vector{32, 8};
  CHECK(bit_vector.value() == 32);
  CHECK(bit_vector.get_sort() == smt_bit_vector_sortt{8});
}

TEST_CASE("smt_termt equality.", "[core][smt2_incremental]")
{
  smt_termt false_term = smt_bool_literal_termt{false};
  CHECK(false_term == false_term);
  CHECK(false_term == smt_bool_literal_termt{false});
  smt_termt true_term = smt_bool_literal_termt{true};
  CHECK_FALSE(false_term == true_term);
  CHECK(
    smt_bit_vector_constant_termt{42, 8} !=
    smt_bit_vector_constant_termt{12, 8});
  smt_termt not_false = smt_not_termt{smt_bool_literal_termt{false}};
  smt_termt not_true = smt_not_termt{smt_bool_literal_termt{true}};
  CHECK_FALSE(not_false == true_term);
  CHECK_FALSE(not_false == not_true);
  CHECK(not_false == smt_not_termt{smt_bool_literal_termt{false}});
}
