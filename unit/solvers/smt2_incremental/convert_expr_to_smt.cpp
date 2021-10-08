// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/format.h>
#include <util/std_expr.h>

TEST_CASE("\"typet\" to smt sort conversion", "[core][smt2_incremental]")
{
  SECTION("Boolean type")
  {
    CHECK(convert_type_to_smt_sort(bool_typet{}) == smt_bool_sortt{});
  }
  SECTION("Bit vector types")
  {
    CHECK(convert_type_to_smt_sort(bv_typet{8}) == smt_bit_vector_sortt{8});
    CHECK(
      convert_type_to_smt_sort(signedbv_typet{16}) == smt_bit_vector_sortt{16});
    CHECK(
      convert_type_to_smt_sort(unsignedbv_typet{32}) ==
      smt_bit_vector_sortt{32});
  }
  SECTION("Error handling")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(convert_type_to_smt_sort(empty_typet{}));
  }
}

TEST_CASE("\"symbol_exprt\" to smt term conversion", "[core][smt2_incremental]")
{
  CHECK(
    convert_expr_to_smt(symbol_exprt{"foo", bool_typet{}}) ==
    smt_identifier_termt("foo", smt_bool_sortt{}));
}

TEST_CASE(
  "\"exprt\" to smt term conversion for constants/literals",
  "[core][smt2_incremental]")
{
  SECTION("Boolean constants")
  {
    CHECK(convert_expr_to_smt(true_exprt{}) == smt_bool_literal_termt{true});
    CHECK(convert_expr_to_smt(false_exprt{}) == smt_bool_literal_termt{false});
  }
  SECTION("Bit vector literals")
  {
    CHECK(
      convert_expr_to_smt(from_integer({12}, signedbv_typet{8})) ==
      smt_bit_vector_constant_termt{12, 8});
    CHECK(
      convert_expr_to_smt(from_integer({24}, unsignedbv_typet{8})) ==
      smt_bit_vector_constant_termt{24, 8});
    CHECK(
      convert_expr_to_smt(from_integer({-1}, signedbv_typet{16})) ==
      smt_bit_vector_constant_termt{65535, 16});
  }
}

TEST_CASE(
  "expr to smt conversion for \"if then else\"",
  "[core][smt2_incremental]")
{
  const auto true_term = smt_bool_literal_termt{true};
  const auto false_term = smt_bool_literal_termt{false};
  CHECK(
    convert_expr_to_smt(if_exprt{true_exprt{}, false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::if_then_else(true_term, false_term, true_term));
  CHECK(
    convert_expr_to_smt(if_exprt{true_exprt{}, true_exprt{}, false_exprt{}}) ==
    smt_core_theoryt::if_then_else(true_term, true_term, false_term));
  CHECK(
    convert_expr_to_smt(if_exprt{false_exprt{}, false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::if_then_else(false_term, false_term, true_term));
  CHECK(
    convert_expr_to_smt(if_exprt{false_exprt{}, true_exprt{}, false_exprt{}}) ==
    smt_core_theoryt::if_then_else(false_term, true_term, false_term));
}

TEST_CASE(
  "expr to smt conversion for \"and\" operator",
  "[core][smt2_incremental]")
{
  const and_exprt binary_and{true_exprt{}, false_exprt{}};
  REQUIRE(
    convert_expr_to_smt(binary_and) ==
    smt_core_theoryt::make_and(
      smt_bool_literal_termt{true}, smt_bool_literal_termt{false}));
  const and_exprt multiary_and{true_exprt{}, true_exprt{}, false_exprt{}};
  REQUIRE(
    convert_expr_to_smt(multiary_and) ==
    smt_core_theoryt::make_and(
      smt_core_theoryt::make_and(
        smt_bool_literal_termt{true}, smt_bool_literal_termt{true}),
      smt_bool_literal_termt{false}));
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS(convert_expr_to_smt(and_exprt{{}}));
  REQUIRE_THROWS(convert_expr_to_smt(and_exprt{{true_exprt{}}}));
}

TEST_CASE(
  "expr to smt conversion for \"or\" operator",
  "[core][smt2_incremental]")
{
  const or_exprt binary_or{true_exprt{}, false_exprt{}};
  REQUIRE(
    convert_expr_to_smt(binary_or) ==
    smt_core_theoryt::make_or(
      smt_bool_literal_termt{true}, smt_bool_literal_termt{false}));
  const or_exprt multiary_or{true_exprt{}, true_exprt{}, false_exprt{}};
  REQUIRE(
    convert_expr_to_smt(multiary_or) ==
    smt_core_theoryt::make_or(
      smt_core_theoryt::make_or(
        smt_bool_literal_termt{true}, smt_bool_literal_termt{true}),
      smt_bool_literal_termt{false}));
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS(convert_expr_to_smt(or_exprt{{}}));
  REQUIRE_THROWS(convert_expr_to_smt(or_exprt{{true_exprt{}}}));
}

TEST_CASE(
  "expr to smt conversion for \"xor\" operator",
  "[core][smt2_incremental]")
{
  const xor_exprt binary_xor{true_exprt{}, false_exprt{}};
  REQUIRE(
    convert_expr_to_smt(binary_xor) ==
    smt_core_theoryt::make_xor(
      smt_bool_literal_termt{true}, smt_bool_literal_termt{false}));
  // Note at the time of writing this test the constructors of xor_exprt only
  // support construction with 2 operands. Therefore, other numbers of operands
  // are untested.
}

TEST_CASE(
  "expr to smt conversion for \"implies\" operator",
  "[core][smt2_incremental]")
{
  REQUIRE(
    convert_expr_to_smt(implies_exprt{false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::implies(
      smt_bool_literal_termt{false}, smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for \"equals\" operator",
  "[core][smt2_incremental]")
{
  REQUIRE(
    convert_expr_to_smt(equal_exprt{false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::equal(
      smt_bool_literal_termt{false}, smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for \"not equals\" operator",
  "[core][smt2_incremental]")
{
  REQUIRE(
    convert_expr_to_smt(notequal_exprt{false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::distinct(
      smt_bool_literal_termt{false}, smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for \"not\" operator",
  "[core][smt2_incremental]")
{
  REQUIRE(
    convert_expr_to_smt(not_exprt{true_exprt{}}) ==
    smt_core_theoryt::make_not(smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for relational operators",
  "[core][smt2_incremental]")
{
  const smt_termt one_term = smt_bit_vector_constant_termt{1, 8};
  const smt_termt two_term = smt_bit_vector_constant_termt{2, 8};
  SECTION("Greater than")
  {
    CHECK(
      convert_expr_to_smt(
        greater_than_exprt{from_integer({1}, signedbv_typet{8}),
                           from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_greater_than(one_term, two_term));
    CHECK(
      convert_expr_to_smt(
        greater_than_exprt{from_integer({1}, unsignedbv_typet{8}),
                           from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_greater_than(one_term, two_term));
  }
  SECTION("Greater than or equal")
  {
    CHECK(
      convert_expr_to_smt(
        greater_than_or_equal_exprt{from_integer({1}, signedbv_typet{8}),
                                    from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_greater_than_or_equal(one_term, two_term));
    CHECK(
      convert_expr_to_smt(
        greater_than_or_equal_exprt{from_integer({1}, unsignedbv_typet{8}),
                                    from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(
        one_term, two_term));
  }
  SECTION("Less than")
  {
    CHECK(
      convert_expr_to_smt(
        less_than_exprt{from_integer({1}, signedbv_typet{8}),
                        from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_less_than(one_term, two_term));
    CHECK(
      convert_expr_to_smt(
        less_than_exprt{from_integer({1}, unsignedbv_typet{8}),
                        from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_less_than(one_term, two_term));
  }
  SECTION("Less than or equal")
  {
    CHECK(
      convert_expr_to_smt(
        less_than_or_equal_exprt{from_integer({1}, signedbv_typet{8}),
                                 from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_less_than_or_equal(one_term, two_term));
    CHECK(
      convert_expr_to_smt(
        less_than_or_equal_exprt{from_integer({1}, unsignedbv_typet{8}),
                                 from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(one_term, two_term));
  }
}
