// Author: Diffblue Ltd.

/// \file
/// Unit tests for smt2_convt

#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/smt2/smt2_conv.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "smt2_convt::convert_identifier character escaping.",
  "[core][solvers][smt2]")
{
  const std::string no_escaping_characters =
    "abcdefghijklmnopqrstuvwxyz0123456789$";
  CHECK(
    smt2_convt::convert_identifier(no_escaping_characters) ==
    no_escaping_characters);
  CHECK(smt2_convt::convert_identifier("\\") == "|&92;|");
  CHECK(smt2_convt::convert_identifier("|") == "|&124;|");
  CHECK(smt2_convt::convert_identifier("&") == "&");
}

/// Helper: extract the "(assert ...)" line from SMT2 output of set_to
static std::string get_assert(const exprt &red_expr)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  std::ostringstream out;
  smt2_convt conv(ns, "test", "", "QF_BV", smt2_convt::solvert::GENERIC, out);
  conv.set_to(red_expr, true);
  std::string result = out.str();
  auto pos = result.find("(assert ");
  REQUIRE(pos != std::string::npos);
  // strip trailing newline
  auto end = result.find_last_not_of('\n');
  return result.substr(pos, end - pos + 1);
}

TEST_CASE("smt2_convt reduction operators", "[core][solvers][smt2]")
{
  unsignedbv_typet u2(2);
  symbol_exprt sym("x", u2);

  SECTION("reduction_and")
  {
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_and, sym}) ==
      "(assert (= x (_ bv3 2)))");
  }

  SECTION("reduction_nand")
  {
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_nand, sym}) ==
      "(assert (not (= x (_ bv3 2))))");
  }

  SECTION("reduction_or")
  {
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_or, sym}) ==
      "(assert (not (= x (_ bv0 2))))");
  }

  SECTION("reduction_nor")
  {
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_nor, sym}) ==
      "(assert (not (not (= x (_ bv0 2)))))");
  }

  SECTION("reduction_xor")
  {
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_xor, sym}) ==
      "(assert (let ((?rop x)) "
      "(= (bvxor ((_ extract 0 0) ?rop) ((_ extract 1 1) ?rop)) #b1)))");
  }

  SECTION("reduction_xnor")
  {
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_xnor, sym}) ==
      "(assert (not (let ((?rop x)) "
      "(= (bvxor ((_ extract 0 0) ?rop) ((_ extract 1 1) ?rop)) #b1))))");
  }

  SECTION("reduction_xor 1-bit")
  {
    symbol_exprt sym1("y", unsignedbv_typet(1));
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_xor, sym1}) ==
      "(assert (= y #b1))");
  }

  SECTION("reduction_and 1-bit")
  {
    symbol_exprt sym1("y", unsignedbv_typet(1));
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_and, sym1}) ==
      "(assert (= y (_ bv1 1)))");
  }

  SECTION("reduction_or 1-bit")
  {
    symbol_exprt sym1("y", unsignedbv_typet(1));
    REQUIRE(
      get_assert(unary_predicate_exprt{ID_reduction_or, sym1}) ==
      "(assert (not (= y (_ bv0 1))))");
  }
}
