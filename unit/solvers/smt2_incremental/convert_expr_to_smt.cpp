// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/constructor_of.h>
#include <util/format.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/object_tracking.h>
#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

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

enum class test_archt
{
  i386,
  x86_64
};

/// \brief Data structures and their initialisation shared between tests.
struct expr_to_smt_conversion_test_environmentt
{
  static expr_to_smt_conversion_test_environmentt make(test_archt arch);
  smt_termt convert(const exprt &expression) const;

  smt_object_mapt object_map;
  smt_object_sizet object_size_function;

private:
  // This is private to ensure the above make() function is used to make
  // correctly configured instances.
  expr_to_smt_conversion_test_environmentt() = default;
};

expr_to_smt_conversion_test_environmentt
expr_to_smt_conversion_test_environmentt::make(test_archt arch)
{
  // Configuration needs to be performed before conversion because pointer
  // widths and object bit width encodings depend on the global configuration.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  switch(arch)
  {
  case test_archt::i386:
    config.ansi_c.set_arch_spec_i386();
    break;
  case test_archt::x86_64:
    config.ansi_c.set_arch_spec_x86_64();
    break;
  default:
    UNREACHABLE;
  }
  return {initial_smt_object_map(), smt_object_sizet{}};
}

smt_termt
expr_to_smt_conversion_test_environmentt::convert(const exprt &expression) const
{
  return convert_expr_to_smt(
    expression, object_map, object_size_function.make_application);
}

TEST_CASE("\"symbol_exprt\" to smt term conversion", "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  CHECK(
    test.convert(symbol_exprt{"foo", bool_typet{}}) ==
    smt_identifier_termt("foo", smt_bool_sortt{}));
}

TEST_CASE(
  "\"exprt\" to smt term conversion for constants/literals",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  SECTION("Boolean constants")
  {
    CHECK(test.convert(true_exprt{}) == smt_bool_literal_termt{true});
    CHECK(test.convert(false_exprt{}) == smt_bool_literal_termt{false});
  }
  SECTION("Bit vector literals")
  {
    CHECK(
      test.convert(from_integer({12}, signedbv_typet{8})) ==
      smt_bit_vector_constant_termt{12, 8});
    CHECK(
      test.convert(from_integer({24}, unsignedbv_typet{8})) ==
      smt_bit_vector_constant_termt{24, 8});
    CHECK(
      test.convert(from_integer({-1}, signedbv_typet{16})) ==
      smt_bit_vector_constant_termt{65535, 16});
  }
  SECTION("Null pointer")
  {
    const smt_termt null_pointer_term =
      smt_bit_vector_constant_termt{0, config.ansi_c.pointer_width};
    CHECK(
      test.convert(null_pointer_exprt{pointer_type(void_type())}) ==
      null_pointer_term);
    CHECK(
      test.convert(null_pointer_exprt{pointer_type(unsignedbv_typet{100})}) ==
      null_pointer_term);
    CHECK(
      test.convert(null_pointer_exprt{
        pointer_type(pointer_type(void_type()))}) == null_pointer_term);
  }
}

TEST_CASE(
  "expr to smt conversion for \"if then else\"",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const auto true_term = smt_bool_literal_termt{true};
  const auto false_term = smt_bool_literal_termt{false};
  CHECK(
    test.convert(if_exprt{true_exprt{}, false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::if_then_else(true_term, false_term, true_term));
  CHECK(
    test.convert(if_exprt{true_exprt{}, true_exprt{}, false_exprt{}}) ==
    smt_core_theoryt::if_then_else(true_term, true_term, false_term));
  CHECK(
    test.convert(if_exprt{false_exprt{}, false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::if_then_else(false_term, false_term, true_term));
  CHECK(
    test.convert(if_exprt{false_exprt{}, true_exprt{}, false_exprt{}}) ==
    smt_core_theoryt::if_then_else(false_term, true_term, false_term));
}

TEST_CASE(
  "expr to smt conversion for \"and\" operator",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const and_exprt binary_and{true_exprt{}, false_exprt{}};
  REQUIRE(
    test.convert(binary_and) ==
    smt_core_theoryt::make_and(
      smt_bool_literal_termt{true}, smt_bool_literal_termt{false}));
  const and_exprt multiary_and{true_exprt{}, true_exprt{}, false_exprt{}};
  REQUIRE(
    test.convert(multiary_and) ==
    smt_core_theoryt::make_and(
      smt_core_theoryt::make_and(
        smt_bool_literal_termt{true}, smt_bool_literal_termt{true}),
      smt_bool_literal_termt{false}));
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS(test.convert(and_exprt{{}}));
  REQUIRE_THROWS(test.convert(and_exprt{{true_exprt{}}}));
}

TEST_CASE(
  "expr to smt conversion for \"or\" operator",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const or_exprt binary_or{true_exprt{}, false_exprt{}};
  REQUIRE(
    test.convert(binary_or) ==
    smt_core_theoryt::make_or(
      smt_bool_literal_termt{true}, smt_bool_literal_termt{false}));
  const or_exprt multiary_or{true_exprt{}, true_exprt{}, false_exprt{}};
  REQUIRE(
    test.convert(multiary_or) ==
    smt_core_theoryt::make_or(
      smt_core_theoryt::make_or(
        smt_bool_literal_termt{true}, smt_bool_literal_termt{true}),
      smt_bool_literal_termt{false}));
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS(test.convert(or_exprt{{}}));
  REQUIRE_THROWS(test.convert(or_exprt{{true_exprt{}}}));
}

TEST_CASE(
  "expr to smt conversion for \"xor\" operator",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const xor_exprt binary_xor{true_exprt{}, false_exprt{}};
  REQUIRE(
    test.convert(binary_xor) ==
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
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  REQUIRE(
    test.convert(implies_exprt{false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::implies(
      smt_bool_literal_termt{false}, smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for \"equals\" operator",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  REQUIRE(
    test.convert(equal_exprt{false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::equal(
      smt_bool_literal_termt{false}, smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for \"not equals\" operator",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  REQUIRE(
    test.convert(notequal_exprt{false_exprt{}, true_exprt{}}) ==
    smt_core_theoryt::distinct(
      smt_bool_literal_termt{false}, smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for \"not\" operator",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  REQUIRE(
    test.convert(not_exprt{true_exprt{}}) ==
    smt_core_theoryt::make_not(smt_bool_literal_termt{true}));
}

TEST_CASE(
  "expr to smt conversion for relational operators",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const smt_termt one_term = smt_bit_vector_constant_termt{1, 8};
  const smt_termt two_term = smt_bit_vector_constant_termt{2, 8};
  SECTION("Greater than")
  {
    CHECK(
      test.convert(greater_than_exprt{
        from_integer({1}, signedbv_typet{8}),
        from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_greater_than(one_term, two_term));
    CHECK(
      test.convert(greater_than_exprt{
        from_integer({1}, unsignedbv_typet{8}),
        from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_greater_than(one_term, two_term));
  }
  SECTION("Greater than or equal")
  {
    CHECK(
      test.convert(greater_than_or_equal_exprt{
        from_integer({1}, signedbv_typet{8}),
        from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_greater_than_or_equal(one_term, two_term));
    CHECK(
      test.convert(greater_than_or_equal_exprt{
        from_integer({1}, unsignedbv_typet{8}),
        from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(
        one_term, two_term));
  }
  SECTION("Less than")
  {
    CHECK(
      test.convert(less_than_exprt{
        from_integer({1}, signedbv_typet{8}),
        from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_less_than(one_term, two_term));
    CHECK(
      test.convert(less_than_exprt{
        from_integer({1}, unsignedbv_typet{8}),
        from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_less_than(one_term, two_term));
  }
  SECTION("Less than or equal")
  {
    CHECK(
      test.convert(less_than_or_equal_exprt{
        from_integer({1}, signedbv_typet{8}),
        from_integer({2}, signedbv_typet{8})}) ==
      smt_bit_vector_theoryt::signed_less_than_or_equal(one_term, two_term));
    CHECK(
      test.convert(less_than_or_equal_exprt{
        from_integer({1}, unsignedbv_typet{8}),
        from_integer({2}, unsignedbv_typet{8})}) ==
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(one_term, two_term));
  }
}

TEST_CASE(
  "expr to smt conversion for arithmetic operators",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const smt_termt smt_term_one = smt_bit_vector_constant_termt{1, 8};
  const smt_termt smt_term_two = smt_bit_vector_constant_termt{2, 8};

  // Just regular (bit-vector) integers, to be used for the comparison
  const auto one_bvint = from_integer({1}, signedbv_typet{8});
  const auto two_bvint = from_integer({2}, signedbv_typet{8});
  const auto one_bvint_unsigned = from_integer({1}, unsignedbv_typet{8});
  const auto two_bvint_unsigned = from_integer({2}, unsignedbv_typet{8});

  SECTION("Addition of two constant size bit-vectors")
  {
    const auto constructed_term =
      test.convert(plus_exprt{one_bvint, two_bvint});
    const auto expected_term =
      smt_bit_vector_theoryt::add(smt_term_one, smt_term_two);
    CHECK(constructed_term == expected_term);
  }

  SECTION(
    "Addition of four constant size bit-vectors - testing multi-ary handling "
    "of plus_exprt")
  {
    const auto three_bv_int = from_integer({3}, signedbv_typet{8});
    const auto four_bv_int = from_integer({4}, signedbv_typet{8});

    const auto three_smt_term = smt_bit_vector_constant_termt{3, 8};
    const auto four_smt_term = smt_bit_vector_constant_termt{4, 8};

    const exprt::operandst plus_operands{
      one_bvint, two_bvint, three_bv_int, four_bv_int};
    const auto constructed_term =
      test.convert(plus_exprt{plus_operands, signedbv_typet{8}});
    const auto expected_term = smt_bit_vector_theoryt::add(
      smt_bit_vector_theoryt::add(
        smt_bit_vector_theoryt::add(smt_term_one, smt_term_two),
        three_smt_term),
      four_smt_term);

    CHECK(constructed_term == expected_term);
  }

  SECTION(
    "Ensure that addition node conversion fails if the operands are not "
    "bit-vector based")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(test.convert(plus_exprt{true_exprt{}, false_exprt{}}));
  }

  SECTION(
    "Ensure that addition node conversion fails if it has a malformed "
    "expression")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    // No operands to expression
    exprt::operandst zero_operands;
    REQUIRE_THROWS(test.convert(plus_exprt{zero_operands, signedbv_typet{8}}));

    // One operand to expression
    const auto four_bv_int = from_integer({4}, signedbv_typet{8});
    exprt::operandst one_operand{four_bv_int};
    REQUIRE_THROWS(test.convert(plus_exprt{one_operand, signedbv_typet{8}}));
  }

  SECTION("Subtraction of two constant size bit-vectors")
  {
    const auto constructed_term =
      test.convert(minus_exprt{two_bvint, one_bvint});
    const auto expected_term =
      smt_bit_vector_theoryt::subtract(smt_term_two, smt_term_one);
    CHECK(constructed_term == expected_term);
  }

  SECTION(
    "Ensure that subtraction node conversion fails if the operands are not "
    "bit-vector based")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(test.convert(minus_exprt{true_exprt{}, false_exprt{}}));
  }

  SECTION("Multiplication of two constant size bit-vectors")
  {
    const auto constructed_term =
      test.convert(mult_exprt{one_bvint, two_bvint});
    const auto expected_term =
      smt_bit_vector_theoryt::multiply(smt_term_one, smt_term_two);
    CHECK(constructed_term == expected_term);
  }

  SECTION(
    "Ensure that multiplication node conversion fails if the operands are not "
    "bit-vector based")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(test.convert(mult_exprt{one_bvint, false_exprt{}}));
  }

  // Division is defined over unsigned numbers only (theory notes say it
  // truncates over zero)
  SECTION("Division of two constant size bit-vectors")
  {
    // Check of division expression with unsigned operands
    const auto constructed_term =
      test.convert(div_exprt{one_bvint_unsigned, two_bvint_unsigned});
    const auto expected_term =
      smt_bit_vector_theoryt::unsigned_divide(smt_term_one, smt_term_two);
    CHECK(constructed_term == expected_term);

    // Check of division expression with signed operands
    const auto constructed_term_signed =
      test.convert(div_exprt{one_bvint, two_bvint});
    const auto expected_term_signed =
      smt_bit_vector_theoryt::signed_divide(smt_term_one, smt_term_two);
    CHECK(constructed_term_signed == expected_term_signed);
  }

  SECTION(
    "Ensure that division node conversion fails if the operands are not "
    "bit-vector based")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(test.convert(div_exprt{one_bvint, false_exprt{}}));
  }

  SECTION(
    "Remainder (modulus) from truncating division of two constant "
    "size bit-vectors")
  {
    // Remainder expression with unsigned operands.
    const auto constructed_term =
      test.convert(mod_exprt{one_bvint_unsigned, two_bvint_unsigned});
    const auto expected_term =
      smt_bit_vector_theoryt::unsigned_remainder(smt_term_one, smt_term_two);
    CHECK(constructed_term == expected_term);

    // Remainder expression with signed operands
    const auto constructed_term_signed =
      test.convert(mod_exprt{one_bvint, two_bvint});
    const auto expected_term_signed =
      smt_bit_vector_theoryt::signed_remainder(smt_term_one, smt_term_two);
    CHECK(constructed_term_signed == expected_term_signed);
  }

  SECTION(
    "Ensure that remainder (truncated modulo) node conversion fails if the "
    "operands are not bit-vector based")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(test.convert(mod_exprt{one_bvint, false_exprt{}}));
  }

  SECTION("Unary minus of constant size bit-vector")
  {
    const auto constructed_term = test.convert(unary_minus_exprt{one_bvint});
    const auto expected_term = smt_bit_vector_theoryt::negate(smt_term_one);
    CHECK(constructed_term == expected_term);
  }

  SECTION(
    "Ensure that unary minus node conversion fails if the operand is not a "
    "bit-vector")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS(test.convert(unary_minus_exprt{true_exprt{}}));
  }
}

SCENARIO(
  "Bitwise \"AND\" expressions are converted to SMT terms",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("three integer bitvectors and their smt-term equivalents")
  {
    const smt_termt smt_term_one = smt_bit_vector_constant_termt{1, 8};
    const smt_termt smt_term_three = smt_bit_vector_constant_termt{3, 8};
    const smt_termt smt_term_five = smt_bit_vector_constant_termt{5, 8};

    const auto one_bvint = from_integer(1, signedbv_typet{8});
    const auto three_bvint = from_integer(3, signedbv_typet{8});
    const auto five_bvint = from_integer(5, signedbv_typet{8});

    WHEN("a bitand_exprt with two of them as arguments is converted")
    {
      const auto constructed_term =
        test.convert(bitand_exprt{one_bvint, three_bvint});

      THEN(
        "it should be equivalent to a \"bvand\" term with the operands "
        "converted as well")
      {
        const auto expected_term =
          smt_bit_vector_theoryt::make_and(smt_term_one, smt_term_three);

        CHECK(constructed_term == expected_term);
      }
    }

    // bitand_exprt derives from multiary exprt, so we need to be able to handle
    // expressions with more than 2 operands.
    WHEN("a ternary bitand_exprt gets connverted to smt terms")
    {
      // We need to jump through a bit of a hoop because bitand_exprt doesn't
      // support direct construction with multiple operands - so we have to
      // construct its parent class and downcast it.
      const exprt::operandst and_operands{one_bvint, three_bvint, five_bvint};
      const multi_ary_exprt first_step{
        ID_bitand, and_operands, signedbv_typet{8}};
      const auto bitand_expr = to_bitand_expr(first_step);

      const auto constructed_term = test.convert(bitand_expr);

      THEN(
        "it should be converted to an appropriate number of nested binary "
        "\"bvand\" terms")
      {
        const auto expected_term = smt_bit_vector_theoryt::make_and(
          smt_bit_vector_theoryt::make_and(smt_term_one, smt_term_three),
          smt_term_five);
        CHECK(constructed_term == expected_term);
      }
    }

    // Both of the above tests have been testing the positive case so far -
    // where everything goes more or less how we expect. Let's see how it
    // does with a negative case - where one of the terms is bad or otherwise
    // unsuitable for expression.
    WHEN("a bitand_exprt with operands of different types gets converted")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception because bvand requires"
        "operands of the same sort")
      {
        CHECK_THROWS(test.convert(bitand_exprt{one_bvint, true_exprt{}}));
      }
    }
  }
}

SCENARIO(
  "Bitwise \"OR\" expressions are converted to SMT terms",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("three integer bitvectors and their smt-term equivalents")
  {
    const smt_termt smt_term_one = smt_bit_vector_constant_termt{1, 8};
    const smt_termt smt_term_three = smt_bit_vector_constant_termt{3, 8};
    const smt_termt smt_term_five = smt_bit_vector_constant_termt{5, 8};

    const auto one_bvint = from_integer(1, signedbv_typet{8});
    const auto three_bvint = from_integer(3, signedbv_typet{8});
    const auto five_bvint = from_integer(5, signedbv_typet{8});

    WHEN("a bitor_exprt with two of them as arguments is converted")
    {
      const auto constructed_term =
        test.convert(bitor_exprt{one_bvint, three_bvint});

      THEN(
        "it should be equivalent to a \"bvor\" term with the operands "
        "converted as well")
      {
        const auto expected_term =
          smt_bit_vector_theoryt::make_or(smt_term_one, smt_term_three);

        CHECK(constructed_term == expected_term);
      }
    }

    // bitor_exprt is similar to bitand_exprt in that it derives from multiary
    // exprt, so we need to be able to handle expressions with more than 2
    // operands. We're going to follow the same format and construct a
    // multiary_exprt as if it was a bitor_exprt, then cast it to one, finally
    // passing it on to convert_expt_to_smt to convert it to an appropriate SMT
    // term.
    WHEN("a ternary bitor_exprt gets connverted to smt terms")
    {
      const exprt::operandst or_operands{one_bvint, three_bvint, five_bvint};
      const multi_ary_exprt first_step{
        ID_bitor, or_operands, signedbv_typet{8}};
      const auto bitor_expr = to_bitor_expr(first_step);

      const auto constructed_term = test.convert(bitor_expr);

      THEN(
        "it should be converted to an appropriate number of nested binary "
        "\"bvor\" terms")
      {
        // In QF_BV, bvor is defined as a binary function, so we need to
        // construct bvor terms with arity > 2 in terms of nested bvor
        // constructs.
        const auto expected_term = smt_bit_vector_theoryt::make_or(
          smt_bit_vector_theoryt::make_or(smt_term_one, smt_term_three),
          smt_term_five);
        CHECK(constructed_term == expected_term);
      }
    }

    // Both of the above tests have been testing the positive case so far -
    // where everything goes more or less how we expect. Let's see how it does
    // with a negative case - where one of the terms is bad or otherwise
    // unsuitable for expression.
    WHEN("a bitor_exprt with operands of different types gets converted")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception because bvor requires"
        "operands of the same sort")
      {
        CHECK_THROWS(test.convert(bitor_exprt{one_bvint, true_exprt{}}));
      }
    }
  }
}

SCENARIO(
  "Bitwise \"XOR\" expressions are converted to SMT terms",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("three integer bitvectors and their smt-term equivalents")
  {
    const smt_termt smt_term_one = smt_bit_vector_constant_termt{1, 8};
    const smt_termt smt_term_three = smt_bit_vector_constant_termt{3, 8};
    const smt_termt smt_term_five = smt_bit_vector_constant_termt{5, 8};

    const auto one_bvint = from_integer(1, signedbv_typet{8});
    const auto three_bvint = from_integer(3, signedbv_typet{8});
    const auto five_bvint = from_integer(5, signedbv_typet{8});

    WHEN("a bitxor_exprt with two of them as arguments is converted")
    {
      const auto constructed_term =
        test.convert(bitxor_exprt{one_bvint, three_bvint});

      THEN(
        "it should be equivalent to a \"bvxor\" term with the operands "
        "converted as well")
      {
        const auto expected_term =
          smt_bit_vector_theoryt::make_xor(smt_term_one, smt_term_three);

        CHECK(constructed_term == expected_term);
      }
    }

    // bitxor_exprt is similar to bitand_exprt and bitor_exprt, so we need
    // to handle the case where we need to convert expressions with arity > 2.
    WHEN("a ternary bitxor_exprt gets connverted to smt terms")
    {
      const exprt::operandst xor_operands{one_bvint, three_bvint, five_bvint};
      const multi_ary_exprt first_step{
        ID_bitxor, xor_operands, signedbv_typet{8}};
      const auto bitxor_expr = to_bitxor_expr(first_step);

      const auto constructed_term = test.convert(bitxor_expr);

      THEN(
        "it should be converted to an appropriate number of nested binary "
        "\"bvxor\" terms")
      {
        // We handle this in much the same way as we do bvand and bvor.
        // See the corresponding comments there.
        const auto expected_term = smt_bit_vector_theoryt::make_xor(
          smt_bit_vector_theoryt::make_xor(smt_term_one, smt_term_three),
          smt_term_five);
        CHECK(constructed_term == expected_term);
      }
    }

    // Both of the above tests have been testing the positive case so far -
    // where everything goes more or less how we expect. Let's see how it does
    // with a negative case - where one of the terms is bad or otherwise
    // unsuitable for expression.
    WHEN("a bitxor_exprt with operands of different types gets converted")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception because bvxor requires"
        "operands of the same sort")
      {
        CHECK_THROWS(test.convert(bitxor_exprt{one_bvint, true_exprt{}}));
      }
    }
  }
}

SCENARIO(
  "Bitwise \"NOT\" expressions are converted to SMT terms (1's complement)",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("An integer bitvector")
  {
    const auto one_bvint = from_integer(1, signedbv_typet{8});

    WHEN("A bitnot_exprt is constructed and converted to an SMT term")
    {
      const auto constructed_term = test.convert(bitnot_exprt{one_bvint});
      THEN("it should be converted to bvnot smt term")
      {
        const smt_termt smt_term_one = smt_bit_vector_constant_termt{1, 8};
        const auto expected_term =
          smt_bit_vector_theoryt::make_not(smt_term_one);

        REQUIRE(constructed_term == expected_term);
      }
    }

    WHEN("A bitnot_exprt is constructed with a false expression and converted")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception and not allow "
        "construction")
      {
        REQUIRE_THROWS(test.convert(bitnot_exprt{false_exprt{}}));
      }
    }
  }
}

SCENARIO(
  "Left-shift expressions are converted to SMT terms",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("An integer bitvector and the number of places we're going to shift")
  {
    // This is going to act as both the value to be shifted, and a value
    // signifying the places to the left we're shifting.
    const auto one_bvint = from_integer(1, signedbv_typet{8});

    WHEN("We construct a shl_exprt and convert it to an SMT term")
    {
      const auto shift_expr = shl_exprt{one_bvint, one_bvint};
      const auto constructed_term = test.convert(shift_expr);

      THEN("It should be equivalent to a bvshl term")
      {
        const smt_termt smt_term_one = smt_bit_vector_constant_termt{1, 8};
        const auto expected_term = smt_bit_vector_theoryt::shift_left(
          /* term */
          smt_term_one,
          /* distance */
          smt_term_one);
      }
    }

    WHEN(
      "We construct a malformed shl_exprt and attempt to convert it to an SMT "
      "term")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception because of validation "
        "failure")
      {
        REQUIRE_THROWS(test.convert(shl_exprt{one_bvint, false_exprt{}}));
      }
    }
  }
}

SCENARIO(
  "Logical Right-shift expressions are converted to SMT terms",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("Two integer bitvectors, one for the value and one for the places")
  {
    const auto to_be_shifted = from_integer(1, signedbv_typet{8});
    const auto places = from_integer(2, signedbv_typet{8});

    WHEN("We construct a lshr_exprt and convert it to an SMT term")
    {
      const auto shift_expr = lshr_exprt{to_be_shifted, places};
      const auto constructed_term = test.convert(shift_expr);

      THEN("We should get an logical shift right SMT term")
      {
        const smt_termt smt_term_value = smt_bit_vector_constant_termt{1, 8};
        const smt_termt smt_term_places = smt_bit_vector_constant_termt{2, 8};
        const auto expected_term = smt_bit_vector_theoryt::logical_shift_right(
          smt_term_value, smt_term_places);
        REQUIRE(constructed_term == expected_term);
      }
    }

    WHEN(
      "We construct a malformed lshr_exprt and attempt to convert it to an SMT"
      " term")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception because of validation "
        "failure")
      {
        REQUIRE_THROWS(test.convert(lshr_exprt{to_be_shifted, false_exprt{}}));
      }
    }
  }
}

SCENARIO(
  "Arithmetic Right-shift expressions are converted to SMT terms",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  GIVEN("Two integer bitvectors, one for the value and one for the places")
  {
    const auto to_be_shifted = from_integer(1, signedbv_typet{8});
    const auto places = from_integer(2, signedbv_typet{8});

    WHEN("We construct a ashr_exprt and convert it to an SMT term")
    {
      const auto shift_expr = ashr_exprt{to_be_shifted, places};
      const auto constructed_term = test.convert(shift_expr);

      THEN("We should get an arithmetic shift-right SMT term")
      {
        const smt_termt smt_term_value = smt_bit_vector_constant_termt{1, 8};
        const smt_termt smt_term_places = smt_bit_vector_constant_termt{2, 8};
        const auto expected_term =
          smt_bit_vector_theoryt::arithmetic_shift_right(
            smt_term_value, smt_term_places);
        REQUIRE(constructed_term == expected_term);
      }
    }

    WHEN("We construct an ashr_exprt and with a shift of 0 places")
    {
      const auto zero_places = from_integer(0, signedbv_typet{8});
      const auto shift_expr = ashr_exprt{to_be_shifted, zero_places};
      const auto constructed_term = test.convert(shift_expr);

      THEN(
        "When we convert it, we should be getting an arithmetic shift-right "
        "term")
      {
        const smt_termt smt_term_value = smt_bit_vector_constant_termt{1, 8};
        const smt_termt smt_term_places = smt_bit_vector_constant_termt{0, 8};
        const auto expected_term =
          smt_bit_vector_theoryt::arithmetic_shift_right(
            smt_term_value, smt_term_places);
        REQUIRE(constructed_term == expected_term);
      }
    }

    WHEN(
      "We construct a malformed ashr_exprt and attempt to convert it to an SMT "
      "term")
    {
      const cbmc_invariants_should_throwt invariants_throw;
      THEN(
        "convert_expr_to_smt should throw an exception because of validation "
        "failure")
      {
        REQUIRE_THROWS(test.convert(ashr_exprt{to_be_shifted, false_exprt{}}));
      }
    }
  }
}

TEST_CASE(
  "expr to smt conversion for shifts of mismatched operands.",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  using make_typet = std::function<typet(std::size_t)>;
  const make_typet make_unsigned = constructor_oft<unsignedbv_typet>{};
  const make_typet make_signed = constructor_oft<signedbv_typet>{};
  using make_extensiont =
    std::function<std::function<smt_termt(smt_termt)>(std::size_t)>;
  const make_extensiont zero_extend = smt_bit_vector_theoryt::zero_extend;
  const make_extensiont sign_extend = smt_bit_vector_theoryt::sign_extend;
  std::string type_description;
  make_typet make_type;
  make_extensiont make_extension;
  using type_rowt = std::tuple<std::string, make_typet, make_extensiont>;
  std::tie(type_description, make_type, make_extension) = GENERATE_REF(
    type_rowt{"Unsigned operands.", make_unsigned, zero_extend},
    type_rowt{"Signed operands.", make_signed, sign_extend});
  SECTION(type_description)
  {
    using make_shift_exprt = std::function<exprt(exprt, exprt)>;
    const make_shift_exprt left_shift_expr = constructor_of<shl_exprt>();
    const make_shift_exprt arithmetic_right_shift_expr =
      constructor_of<ashr_exprt>();
    const make_shift_exprt logical_right_shift_expr =
      constructor_of<lshr_exprt>();
    using make_shift_termt = std::function<smt_termt(smt_termt, smt_termt)>;
    const make_shift_termt left_shift_term = smt_bit_vector_theoryt::shift_left;
    const make_shift_termt arithmetic_right_shift_term =
      smt_bit_vector_theoryt::arithmetic_shift_right;
    const make_shift_termt logical_right_shift_term =
      smt_bit_vector_theoryt::logical_shift_right;
    std::string shift_description;
    make_shift_exprt make_shift_expr;
    make_shift_termt make_shift_term;
    using shift_rowt =
      std::tuple<std::string, make_shift_exprt, make_shift_termt>;
    std::tie(shift_description, make_shift_expr, make_shift_term) =
      GENERATE_REF(
        shift_rowt{"Left shift.", left_shift_expr, left_shift_term},
        shift_rowt{
          "Arithmetic right shift.",
          arithmetic_right_shift_expr,
          arithmetic_right_shift_term},
        shift_rowt{
          "Logical right shift.",
          logical_right_shift_expr,
          logical_right_shift_term});
    SECTION(shift_description)
    {
      SECTION("Wider left hand side")
      {
        const exprt input = make_shift_expr(
          symbol_exprt{"foo", make_type(32)},
          symbol_exprt{"bar", make_type(8)});
        INFO("Input expr: " + input.pretty(2, 0));
        const smt_termt expected_result = make_shift_term(
          smt_identifier_termt{"foo", smt_bit_vector_sortt{32}},
          make_extension(24)(
            smt_identifier_termt{"bar", smt_bit_vector_sortt{8}}));
        CHECK(test.convert(input) == expected_result);
      }
      SECTION("Wider right hand side")
      {
        const exprt input = make_shift_expr(
          symbol_exprt{"foo", make_type(8)},
          symbol_exprt{"bar", make_type(32)});
        INFO("Input expr: " + input.pretty(2, 0));
        const smt_termt expected_result = make_shift_term(
          make_extension(24)(
            smt_identifier_termt{"foo", smt_bit_vector_sortt{8}}),
          smt_identifier_termt{"bar", smt_bit_vector_sortt{32}});
        CHECK(test.convert(input) == expected_result);
      }
    }
  }
}

TEST_CASE(
  "expr to smt conversion for extract bits expressions",
  "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const typet operand_type = unsignedbv_typet{8};
  std::string description;
  exprt input;
  using rowt = std::pair<std::string, exprt>;
  std::tie(description, input) = GENERATE_REF(
    rowt{
      "Bit vector typed bounds",
      extractbits_exprt{
        symbol_exprt{"foo", operand_type},
        from_integer(4, operand_type),
        from_integer(2, operand_type),
        unsignedbv_typet{3}}},
    rowt{
      "Constant integer bounds",
      extractbits_exprt{
        symbol_exprt{"foo", operand_type}, 4, 2, unsignedbv_typet{3}}});
  const smt_termt expected_result = smt_bit_vector_theoryt::extract(4, 2)(
    smt_identifier_termt{"foo", smt_bit_vector_sortt{8}});
  SECTION(description)
  {
    INFO("Input expression - " + input.pretty(1, 0));
    CHECK(test.convert(input) == expected_result);
    const cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(test.convert(extractbits_exprt{
      symbol_exprt{"foo", operand_type},
      symbol_exprt{"bar", operand_type},
      symbol_exprt{"bar", operand_type},
      unsignedbv_typet{3}}));
  }
}

TEST_CASE("expr to smt conversion for type casts", "[core][smt2_incremental]")
{
  auto test = expr_to_smt_conversion_test_environmentt::make(test_archt::i386);
  const symbol_exprt bool_expr{"foo", bool_typet{}};
  const smt_termt bool_term = smt_identifier_termt{"foo", smt_bool_sortt{}};
  const symbol_exprt bv_expr{"bar", signedbv_typet(12)};
  const smt_termt bv_term =
    smt_identifier_termt{"bar", smt_bit_vector_sortt{12}};
  SECTION("Casts to bool")
  {
    CHECK(test.convert(typecast_exprt{bool_expr, bool_typet{}}) == bool_term);
    CHECK(
      test.convert(typecast_exprt{bv_expr, bool_typet{}}) ==
      smt_core_theoryt::distinct(
        bv_term, smt_bit_vector_constant_termt{0, 12}));
  }
  SECTION("Casts to C bool")
  {
    const std::size_t c_bool_width = config.ansi_c.bool_width;
    const smt_bit_vector_constant_termt c_true{1, c_bool_width};
    const smt_bit_vector_constant_termt c_false{0, c_bool_width};
    SECTION("from bool")
    {
      const auto cast_bool =
        test.convert(typecast_exprt{bool_expr, c_bool_type()});
      const auto expected_bool_conversion =
        smt_core_theoryt::if_then_else(bool_term, c_true, c_false);
      CHECK(cast_bool == expected_bool_conversion);
    }
    SECTION("from bit vector")
    {
      const auto cast_bit_vector =
        test.convert(typecast_exprt{bv_expr, c_bool_type()});
      const auto expected_bit_vector_conversion =
        smt_core_theoryt::if_then_else(
          smt_core_theoryt::distinct(
            bv_term, smt_bit_vector_constant_termt{0, 12}),
          c_true,
          c_false);
      CHECK(cast_bit_vector == expected_bit_vector_conversion);
    }
  }
  SECTION("Casts to bit vector")
  {
    SECTION("Matched width casts")
    {
      typet from_type, to_type;
      using rowt = std::pair<typet, typet>;
      std::tie(from_type, to_type) = GENERATE(
        rowt{unsignedbv_typet{8}, unsignedbv_typet{8}},
        rowt{unsignedbv_typet{8}, signedbv_typet{8}},
        rowt{signedbv_typet{8}, unsignedbv_typet{8}});
      CHECK(
        test.convert(typecast_exprt{from_integer(1, from_type), to_type}) ==
        smt_bit_vector_constant_termt{1, 8});
    }
    SECTION("Narrowing casts")
    {
      CHECK(
        test.convert(typecast_exprt{bv_expr, signedbv_typet{8}}) ==
        smt_bit_vector_theoryt::extract(7, 0)(bv_term));
      CHECK(
        test.convert(typecast_exprt{
          from_integer(42, unsignedbv_typet{32}), unsignedbv_typet{16}}) ==
        smt_bit_vector_theoryt::extract(15, 0)(
          smt_bit_vector_constant_termt{42, 32}));
    }
    SECTION("Widening casts")
    {
      std::size_t from_width, to_width, extension_width;
      using size_rowt = std::tuple<std::size_t, std::size_t, std::size_t>;
      std::tie(from_width, to_width, extension_width) = GENERATE(
        size_rowt{8, 64, 56}, size_rowt{16, 32, 16}, size_rowt{16, 128, 112});
      PRECONDITION(from_width < to_width);
      PRECONDITION(to_width - from_width == extension_width);
      using make_typet = std::function<typet(std::size_t)>;
      const make_typet make_unsigned = constructor_oft<unsignedbv_typet>{};
      const make_typet make_signed = constructor_oft<signedbv_typet>{};
      using make_extensiont =
        std::function<std::function<smt_termt(smt_termt)>(std::size_t)>;
      const make_extensiont zero_extend = smt_bit_vector_theoryt::zero_extend;
      const make_extensiont sign_extend = smt_bit_vector_theoryt::sign_extend;
      make_typet make_source_type, make_destination_type;
      make_extensiont make_extension;
      using types_rowt = std::tuple<make_typet, make_typet, make_extensiont>;
      std::tie(make_source_type, make_destination_type, make_extension) =
        GENERATE_REF(
          types_rowt{make_unsigned, make_unsigned, zero_extend},
          types_rowt{make_signed, make_signed, sign_extend},
          types_rowt{make_signed, make_unsigned, sign_extend},
          types_rowt{make_unsigned, make_signed, zero_extend});
      const typecast_exprt cast{
        from_integer(42, make_source_type(from_width)),
        make_destination_type(to_width)};
      const smt_termt expected_term = make_extension(extension_width)(
        smt_bit_vector_constant_termt{42, from_width});
      CHECK(test.convert(cast) == expected_term);
    }
    SECTION("from bool")
    {
      const exprt from_expr = GENERATE(
        exprt{symbol_exprt{"baz", bool_typet{}}},
        exprt{true_exprt{}},
        exprt{false_exprt{}});
      const smt_termt from_term = test.convert(from_expr);
      const std::size_t width = GENERATE(1, 8, 16, 32, 64);
      const typecast_exprt cast{from_expr, bitvector_typet{ID_bv, width}};
      CHECK(
        test.convert(cast) == smt_core_theoryt::if_then_else(
                                from_term,
                                smt_bit_vector_constant_termt{1, width},
                                smt_bit_vector_constant_termt{0, width}));
    }
  }
}

TEST_CASE(
  "expr to smt conversion for address of operator",
  "[core][smt2_incremental]")
{
  auto test =
    expr_to_smt_conversion_test_environmentt::make(test_archt::x86_64);
  const symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  const symbol_exprt foo{"foo", unsignedbv_typet{32}};
  const symbol_exprt bar{"bar", unsignedbv_typet{32}};
  SECTION("Address of symbol")
  {
    const address_of_exprt address_of_foo{foo};
    track_expression_objects(address_of_foo, ns, test.object_map);
    INFO("Expression " + address_of_foo.pretty(1, 0));
    SECTION("8 object bits")
    {
      config.bv_encoding.object_bits = 8;
      const auto converted = test.convert(address_of_foo);
      CHECK(test.object_map.at(foo).unique_id == 1);
      CHECK(
        converted == smt_bit_vector_theoryt::concat(
                       smt_bit_vector_constant_termt{1, 8},
                       smt_bit_vector_constant_termt{0, 56}));
    }
    SECTION("16 object bits")
    {
      config.bv_encoding.object_bits = 16;
      const auto converted = test.convert(address_of_foo);
      CHECK(test.object_map.at(foo).unique_id == 1);
      CHECK(
        converted == smt_bit_vector_theoryt::concat(
                       smt_bit_vector_constant_termt{1, 16},
                       smt_bit_vector_constant_termt{0, 48}));
    }
  }
  SECTION("Invariant checks")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    SECTION("Address of should result in a pointer")
    {
      exprt address_of = address_of_exprt{foo};
      address_of.type() = bool_typet{};
      REQUIRE_THROWS_MATCHES(
        test.convert(address_of),
        invariant_failedt,
        invariant_failure_containing(
          "Result of the address_of operator should have pointer type."));
    }
    SECTION("Objects should already be tracked")
    {
      REQUIRE_THROWS_MATCHES(
        test.convert(address_of_exprt{foo}),
        invariant_failedt,
        invariant_failure_containing("Objects should be tracked before "
                                     "converting their address to SMT terms"));
    }
    SECTION("There should be enough bits for object id")
    {
      config.bv_encoding.object_bits = 8;
      const address_of_exprt address_of_foo{foo};
      track_expression_objects(address_of_foo, ns, test.object_map);
      test.object_map.at(foo).unique_id = 256;
      REQUIRE_THROWS_MATCHES(
        test.convert(address_of_exprt{foo}),
        invariant_failedt,
        invariant_failure_containing("There should be sufficient bits to "
                                     "encode unique object identifier."));
    }
    SECTION("Pointer should be wide enough to encode offset")
    {
      config.bv_encoding.object_bits = 64;
      const address_of_exprt address_of_foo{foo};
      track_expression_objects(address_of_foo, ns, test.object_map);
      test.object_map.at(foo).unique_id = 256;
      REQUIRE_THROWS_MATCHES(
        test.convert(address_of_exprt{foo}),
        invariant_failedt,
        invariant_failure_containing("Pointer should be wider than object_bits "
                                     "in order to allow for offset encoding."));
    }
  }
  SECTION("Comparison of address of operations.")
  {
    config.bv_encoding.object_bits = 8;
    const exprt comparison =
      notequal_exprt{address_of_exprt{foo}, address_of_exprt{bar}};
    track_expression_objects(comparison, ns, test.object_map);
    INFO("Expression " + comparison.pretty(1, 0));
    const auto converted = test.convert(comparison);
    CHECK(test.object_map.at(foo).unique_id == 2);
    CHECK(test.object_map.at(bar).unique_id == 1);
    CHECK(
      converted == smt_core_theoryt::distinct(
                     smt_bit_vector_theoryt::concat(
                       smt_bit_vector_constant_termt{2, 8},
                       smt_bit_vector_constant_termt{0, 56}),
                     smt_bit_vector_theoryt::concat(
                       smt_bit_vector_constant_termt{1, 8},
                       smt_bit_vector_constant_termt{0, 56})));
  }
}

TEST_CASE(
  "expr to smt conversion for pointer object expression",
  "[core][smt2_incremental]")
{
  auto test =
    expr_to_smt_conversion_test_environmentt::make(test_archt::x86_64);
  CHECK(config.bv_encoding.object_bits == 8);

  const auto pointer_type = pointer_typet(unsigned_int_type(), 64 /* bits */);
  const pointer_object_exprt foo{
    symbol_exprt{"foo", pointer_type}, pointer_type};
  const pointer_object_exprt foobar{
    symbol_exprt{"foobar", pointer_type}, pointer_type};

  SECTION("Pointer object expression")
  {
    const auto converted = test.convert(foo);
    const auto expected =
      smt_bit_vector_theoryt::zero_extend(56)(smt_bit_vector_theoryt::extract(
        63, 56)(smt_identifier_termt("foo", smt_bit_vector_sortt(64))));
    CHECK(converted == expected);
  }

  SECTION("Invariant checks")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    SECTION("Pointer object's operand type should be a bitvector type")
    {
      auto copy_of_foo = foo;
      copy_of_foo.type() = bool_typet{};
      REQUIRE_THROWS_MATCHES(
        test.convert(copy_of_foo),
        invariant_failedt,
        invariant_failure_containing(
          "Pointer object should have a bitvector-based type."));
    }
  }

  SECTION("Comparison of pointer objects.")
  {
    const exprt comparison = notequal_exprt{foobar, foo};
    INFO("Expression " + comparison.pretty(1, 0));
    const auto converted = test.convert(comparison);
    const auto bv1 =
      smt_bit_vector_theoryt::zero_extend(56)(smt_bit_vector_theoryt::extract(
        63, 56)(smt_identifier_termt("foo", smt_bit_vector_sortt(64))));
    const auto bv2 =
      smt_bit_vector_theoryt::zero_extend(56)(smt_bit_vector_theoryt::extract(
        63, 56)(smt_identifier_termt("foobar", smt_bit_vector_sortt(64))));
    const auto expected = smt_core_theoryt::distinct(bv2, bv1);
    CHECK(converted == expected);
  }
}

TEST_CASE("pointer_offset_exprt to SMT conversion", "[core][smt2_incremental]")
{
  auto test =
    expr_to_smt_conversion_test_environmentt::make(test_archt::x86_64);
  CHECK(config.bv_encoding.object_bits == 8);

  const auto pointer_type = pointer_typet(unsigned_int_type(), 64 /* bits */);
  const pointer_offset_exprt pointer_offset{
    symbol_exprt{"foo", pointer_type}, pointer_type};

  SECTION("simple pointer_offset_exprt conversion")
  {
    const auto converted = test.convert(pointer_offset);
    const auto expected =
      smt_bit_vector_theoryt::zero_extend(8)(smt_bit_vector_theoryt::extract(
        55, 0)(smt_identifier_termt("foo", smt_bit_vector_sortt(64))));
    CHECK(converted == expected);
  }

  SECTION("Invariant checks")
  {
    const cbmc_invariants_should_throwt invariants_throw;
    SECTION("pointer_offset_exprt's operand type should be a bitvector type")
    {
      auto pointer_offset_copy = pointer_offset;
      pointer_offset_copy.type() = bool_typet{};
      REQUIRE_THROWS_MATCHES(
        test.convert(pointer_offset_copy),
        invariant_failedt,
        invariant_failure_containing(
          "Pointer offset should have a bitvector-based type."));
    }
  }
}
