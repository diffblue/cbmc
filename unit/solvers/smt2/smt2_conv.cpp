// Author: Diffblue Ltd.

#include <util/bitvector_expr.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/smt2/smt2_conv.h>
#include <testing-utils/use_catch.h>

#include <sstream>

/// helper class for testing smt2_convt
class smt2_conv_testt : public smt2_convt
{
public:
  smt2_conv_testt(const namespacet &_ns, std::ostream &_out)
    : smt2_convt{_ns, "", "", "", smt2_convt::solvert::GENERIC, _out}
  {
  }

  void convert_expr_public(const exprt &expr)
  {
    convert_expr(expr);
  }
};

static std::string smt2(const exprt &expr)
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  std::ostringstream out;
  smt2_conv_testt smt2_conv{ns, out};
  std::size_t length = out.str().size();
  smt2_conv.convert_expr_public(expr);
  return std::string{out.str(), length, std::string::npos};
}

TEST_CASE("smt2_convt conversion for shifts", "[core][solvers][smt2]")
{
  GIVEN("A shift expression with equal-with operands")
  {
    auto op = symbol_exprt{"op", unsignedbv_typet{8}};
    auto distance = symbol_exprt{"dist", unsignedbv_typet{8}};
    auto shift = shl_exprt{op, distance};
    REQUIRE(smt2(shift) == "(bvshl op dist)");
  }

  GIVEN("A shift expression with an unsigned shift operand and wider distance")
  {
    auto op = symbol_exprt{"op", unsignedbv_typet{8}};
    auto distance = symbol_exprt{"dist", unsignedbv_typet{10}};
    auto shift = shl_exprt{op, distance};
    REQUIRE(
      smt2(shift) == "((_ extract 7 0) (bvshl ((_ zero_extend 2) op) dist))");
  }

  GIVEN("A shift expression with a signed shift operand and wider distance")
  {
    auto op = symbol_exprt{"op", signedbv_typet{8}};
    auto distance = symbol_exprt{"dist", unsignedbv_typet{10}};
    auto shift = ashr_exprt{op, distance};
    REQUIRE(
      smt2(shift) == "((_ extract 7 0) (bvashr ((_ sign_extend 2) op) dist))");
  }

  GIVEN("A shift expression with a wider shift operand")
  {
    auto op = symbol_exprt{"op", unsignedbv_typet{10}};
    auto distance = symbol_exprt{"dist", unsignedbv_typet{8}};
    auto shift = shl_exprt{op, distance};
    REQUIRE(smt2(shift) == "(bvshl op ((_ zero_extend 2) dist))");
  }
}

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
