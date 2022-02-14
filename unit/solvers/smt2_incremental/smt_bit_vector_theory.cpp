// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/mp_arith.h>

TEST_CASE("SMT bit vector concatenation", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt a_valid{42, 8}, b_valid{42, 16};
  SECTION("Valid operands")
  {
    const auto concat = smt_bit_vector_theoryt::concat(a_valid, b_valid);
    const auto expected_return_sort = smt_bit_vector_sortt{24};
    REQUIRE(
      concat.function_identifier() ==
      smt_identifier_termt("concat", expected_return_sort));
    REQUIRE(concat.get_sort() == expected_return_sort);
    REQUIRE(concat.arguments().size() == 2);
    REQUIRE(concat.arguments()[0].get() == a_valid);
    REQUIRE(concat.arguments()[1].get() == b_valid);
  }
  SECTION("Invalid operands")
  {
    const smt_bool_literal_termt false_term{false};
    const smt_bool_literal_termt true_term{true};
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::concat(a_valid, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::concat(false_term, a_valid));
    CHECK_THROWS(smt_bit_vector_theoryt::concat(false_term, true_term));
  }
}

TEST_CASE("SMT bit vector extract", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt operand{42, 8};
  const auto extract_4_3 = smt_bit_vector_theoryt::extract(4, 3);
  SECTION("Valid construction")
  {
    const auto extraction = extract_4_3(operand);
    const auto expected_return_sort = smt_bit_vector_sortt{2};
    REQUIRE(
      extraction.function_identifier() ==
      smt_identifier_termt(
        "extract",
        expected_return_sort,
        {smt_numeral_indext{4}, smt_numeral_indext{3}}));
    REQUIRE(extraction.get_sort() == expected_return_sort);
    REQUIRE(extraction.arguments().size() == 1);
    REQUIRE(extraction.arguments()[0].get() == operand);
  }
  SECTION("Invalid constructions")
  {
    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::extract(3, 4));
    REQUIRE_THROWS(extract_4_3(smt_bool_literal_termt{true}));
    REQUIRE_THROWS(extract_4_3(smt_bit_vector_constant_termt{8, 4}));
  }
}

TEST_CASE("SMT bit vector bitwise operators", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt two{2, 8};
  const smt_bit_vector_constant_termt three{3, 8};
  const smt_bit_vector_constant_termt wider{4, 16};
  const smt_bool_literal_termt true_val{true};
  SECTION("not")
  {
    const auto function_application = smt_bit_vector_theoryt::make_not(two);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvnot", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 1);
    REQUIRE(function_application.arguments()[0].get() == two);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_not(true_val));
  }
  SECTION("or")
  {
    const auto function_application =
      smt_bit_vector_theoryt::make_or(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvor", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_or(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_or(true_val, three));
  }
  SECTION("and")
  {
    const auto function_application =
      smt_bit_vector_theoryt::make_and(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvand", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_and(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_and(true_val, three));
  }
  SECTION("nand")
  {
    const auto function_application = smt_bit_vector_theoryt::nand(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvnand", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::nand(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::nand(true_val, three));
  }
  SECTION("nor")
  {
    const auto function_application = smt_bit_vector_theoryt::nor(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvnor", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::nor(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::nor(true_val, three));
  }
  SECTION("xor")
  {
    const auto function_application =
      smt_bit_vector_theoryt::make_xor(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvxor", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_xor(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::make_xor(true_val, three));
  }
  SECTION("xnor")
  {
    const auto function_application = smt_bit_vector_theoryt::xnor(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvxnor", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::xnor(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::xnor(true_val, three));
  }
}

TEST_CASE("SMT bit vector comparison", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt a_valid{42, 16}, b_valid{8, 16};
  SECTION("Valid operands")
  {
    const auto compare = smt_bit_vector_theoryt::compare(a_valid, b_valid);
    const auto expected_return_sort = smt_bit_vector_sortt{1};
    REQUIRE(
      compare.function_identifier() ==
      smt_identifier_termt("bvcomp", expected_return_sort));
    REQUIRE(compare.get_sort() == expected_return_sort);
    REQUIRE(compare.arguments().size() == 2);
    REQUIRE(compare.arguments()[0].get() == a_valid);
    REQUIRE(compare.arguments()[1].get() == b_valid);
  }
  SECTION("Invalid operands")
  {
    const smt_bool_literal_termt false_term{false};
    const smt_bool_literal_termt true_term{true};
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::compare(a_valid, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::compare(false_term, a_valid));
    CHECK_THROWS(smt_bit_vector_theoryt::compare(false_term, true_term));
  }
}

TEST_CASE("SMT bit vector predicates", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt two{2, 8};
  const smt_bit_vector_constant_termt three{3, 8};
  const smt_bool_literal_termt false_term{false};
  const smt_bit_vector_constant_termt wider{2, 16};
  SECTION("unsigned less than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_less_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvult", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(false_term, two));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(two, wider));
  }
  SECTION("unsigned less than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvule", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(two, false_term));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(wider, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(two, wider));
  }
  SECTION("unsigned greater than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_greater_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvugt", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_greater_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_greater_than(two, wider));
  }
  SECTION("unsigned greater than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvuge", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(two, false_term));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(wider, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(two, wider));
  }
  SECTION("signed less than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_less_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvslt", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(false_term, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(two, wider));
  }
  SECTION("signed less than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_less_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsle", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_less_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_less_than_or_equal(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than_or_equal(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than_or_equal(two, wider));
  }
  SECTION("signed greater than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_greater_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsgt", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(false_term, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(two, wider));
  }
  SECTION("signed greater than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_greater_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsge", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(two, false_term));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(wider, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(two, wider));
  }
}

TEST_CASE(
  "SMT bit vector arithmetic operator implementation tests",
  "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt two{2, 8};
  const smt_bit_vector_constant_termt three{3, 8};
  const smt_bit_vector_constant_termt four{4, 16};
  const smt_bool_literal_termt true_val{true};

  SECTION("Addition")
  {
    const auto function_application = smt_bit_vector_theoryt::add(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvadd", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::add(three, four));
    // An addition of a bool and a bitvector should hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::add(three, true_val));
  }

  SECTION("Subtraction")
  {
    const auto function_application =
      smt_bit_vector_theoryt::subtract(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsub", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::subtract(three, four));
    // A subtraction of a bool and a bitvector should hit an
    // invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::subtract(true_val, three));
  }

  SECTION("Multiplication")
  {
    const auto function_application =
      smt_bit_vector_theoryt::multiply(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvmul", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::multiply(three, four));
    // A multiplication of a bool and a bitvector should hit an
    // invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::multiply(true_val, three));
  }

  SECTION("Unsigned Division")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_divide(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvudiv", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::unsigned_divide(three, four));
    // A division of a bool and a bitvector should hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::unsigned_divide(true_val, three));
  }

  SECTION("Signed Division")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_divide(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsdiv", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::signed_divide(three, four));
    // A division of a bool and a bitvector should hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::signed_divide(true_val, three));
  }

  SECTION("Unsigned Remainder")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_remainder(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvurem", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::unsigned_remainder(three, four));
    // A remainder of a bool and a bitvector should hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::unsigned_remainder(true_val, three));
  }

  SECTION("Signed Remainder")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_remainder(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsrem", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    // Bit-vectors of mismatched sorts are going to hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::signed_remainder(three, four));
    // A remainder of a bool and a bitvector should hit an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::signed_remainder(true_val, three));
  }

  SECTION("Unary Minus")
  {
    const auto function_application = smt_bit_vector_theoryt::negate(two);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvneg", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 1);
    REQUIRE(function_application.arguments()[0].get() == two);

    cbmc_invariants_should_throwt invariants_throw;
    // Negation of a value of bool sort should fail with an invariant violation.
    REQUIRE_THROWS(smt_bit_vector_theoryt::negate(true_val));
  }
}

TEST_CASE("SMT bit vector shifts", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt two{2, 8};
  const smt_bit_vector_constant_termt three{3, 8};
  const smt_bit_vector_constant_termt wider{4, 16};
  const smt_bool_literal_termt true_val{true};
  SECTION("shift left")
  {
    const auto function_application =
      smt_bit_vector_theoryt::shift_left(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvshl", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::shift_left(three, wider));
    REQUIRE_THROWS(smt_bit_vector_theoryt::shift_left(true_val, three));
  }
  SECTION("logical shift right")
  {
    const auto function_application =
      smt_bit_vector_theoryt::logical_shift_right(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvlshr", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(smt_bit_vector_theoryt::logical_shift_right(three, wider));
    REQUIRE_THROWS(
      smt_bit_vector_theoryt::logical_shift_right(true_val, three));
  }
  SECTION("arithmetic shift right")
  {
    const auto function_application =
      smt_bit_vector_theoryt::arithmetic_shift_right(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvashr", smt_bit_vector_sortt{8}));
    REQUIRE(function_application.get_sort() == smt_bit_vector_sortt{8});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);

    cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(
      smt_bit_vector_theoryt::arithmetic_shift_right(three, wider));
    REQUIRE_THROWS(
      smt_bit_vector_theoryt::arithmetic_shift_right(true_val, three));
  }
}

TEST_CASE("SMT bit vector repeat", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt two{2, 8};
  const auto expected_return_sort = smt_bit_vector_sortt{32};
  const smt_bool_literal_termt true_val{true};
  const auto function_application = smt_bit_vector_theoryt::repeat(4)(two);
  REQUIRE(
    function_application.function_identifier() ==
    smt_identifier_termt(
      "repeat", expected_return_sort, {smt_numeral_indext{4}}));
  REQUIRE(function_application.get_sort() == expected_return_sort);
  REQUIRE(function_application.arguments().size() == 1);
  REQUIRE(function_application.arguments()[0].get() == two);
  cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS(smt_bit_vector_theoryt::repeat(0));
  REQUIRE_THROWS(smt_bit_vector_theoryt::repeat(1)(true_val));
}
