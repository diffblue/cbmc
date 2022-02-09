// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_core_theory.h>
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

TEST_CASE("smt_identifier_termt construction", "[core][smt2_incremental]")
{
  cbmc_invariants_should_throwt invariants_throw;
  CHECK_NOTHROW(smt_identifier_termt{"foo bar", smt_bool_sortt{}});
  CHECK_THROWS(smt_identifier_termt{"|foo bar|", smt_bool_sortt{}});
  CHECK_NOTHROW(smt_identifier_termt{"foo\\ bar", smt_bool_sortt{}});
}

TEST_CASE("smt_identifier_termt getters.", "[core][smt2_incremental]")
{
  SECTION("Simple identifier")
  {
    const smt_identifier_termt identifier{"foo", smt_bool_sortt{}};
    CHECK(identifier.identifier() == "foo");
    CHECK(identifier.get_sort() == smt_bool_sortt{});
    CHECK(identifier.indices().empty());
  }
  SECTION("Indexed identifier")
  {
    const smt_symbol_indext baz{"baz"};
    const smt_numeral_indext index_42{42};
    const smt_identifier_termt indexed{
      "bar", smt_bit_vector_sortt{8}, {baz, index_42}};
    CHECK(indexed.identifier() == "bar");
    CHECK(indexed.get_sort() == smt_bit_vector_sortt{8});
    const auto indices = indexed.indices();
    REQUIRE(indices.size() == 2);
    CHECK(indices[0].get() == baz);
    CHECK(indices[1].get() == index_42);
  }
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
}

template <typename expected_termt>
class term_visit_type_checkert final : public smt_term_const_downcast_visitort
{
public:
  bool expected_term_visited = false;
  bool unexpected_term_visited = false;

  void visit(const smt_bool_literal_termt &) override
  {
    if(std::is_same<expected_termt, smt_bool_literal_termt>::value)
    {
      expected_term_visited = true;
    }
    else
    {
      unexpected_term_visited = true;
    }
  }

  void visit(const smt_identifier_termt &) override
  {
    if(std::is_same<expected_termt, smt_identifier_termt>::value)
    {
      expected_term_visited = true;
    }
    else
    {
      unexpected_term_visited = true;
    }
  }

  void visit(const smt_bit_vector_constant_termt &) override
  {
    if(std::is_same<expected_termt, smt_bit_vector_constant_termt>::value)
    {
      expected_term_visited = true;
    }
    else
    {
      unexpected_term_visited = true;
    }
  }

  void visit(const smt_function_application_termt &) override
  {
    if(std::is_same<expected_termt, smt_function_application_termt>::value)
    {
      expected_term_visited = true;
    }
    else
    {
      unexpected_term_visited = true;
    }
  }
};

template <typename term_typet>
term_typet make_test_term();

template <>
smt_bool_literal_termt make_test_term<smt_bool_literal_termt>()
{
  return smt_bool_literal_termt{false};
}

template <>
smt_identifier_termt make_test_term<smt_identifier_termt>()
{
  return smt_identifier_termt{"foo", smt_bool_sortt{}};
}

template <>
smt_bit_vector_constant_termt make_test_term<smt_bit_vector_constant_termt>()
{
  return smt_bit_vector_constant_termt{0, 32};
}

template <>
smt_function_application_termt make_test_term<smt_function_application_termt>()
{
  return smt_core_theoryt::make_not(smt_bool_literal_termt{true});
}

TEMPLATE_TEST_CASE(
  "smt_termt::accept(visitor)",
  "[core][smt2_incremental]",
  smt_bool_literal_termt,
  smt_identifier_termt,
  smt_bit_vector_constant_termt,
  smt_function_application_termt)
{
  term_visit_type_checkert<TestType> checker;
  make_test_term<TestType>().accept(checker);
  CHECK(checker.expected_term_visited);
  CHECK_FALSE(checker.unexpected_term_visited);
}
