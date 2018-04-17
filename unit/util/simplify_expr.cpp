/*******************************************************************\

 Module: Unit tests of the expression simplifier

 Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <java_bytecode/java_types.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <limits>

namespace
{
exprt test_float_expr(
  irep_idt operator_type,
  float op1,
  float op2,
  ieee_floatt::rounding_modet rounding_mode = ieee_floatt::ROUND_TO_EVEN)
{
  config.set_arch("none");
  symbol_tablet symbol_table;
  symbolt cprover_rounding_mode;
  cprover_rounding_mode.base_name = "__CPROVER_rounding_mode";
  cprover_rounding_mode.name = "__CPROVER_rounding_mode";
  cprover_rounding_mode.pretty_name = "__CPROVER_rounding_mode";
  cprover_rounding_mode.value = from_integer(rounding_mode, integer_typet());
  cprover_rounding_mode.type = cprover_rounding_mode.value.type();
  cprover_rounding_mode.is_static_lifetime = true;
  symbol_table.add(cprover_rounding_mode);
  namespacet ns(symbol_table);
  ieee_floatt f1;
  f1.from_float(op1);
  ieee_floatt f2;
  f2.from_float(op2);

  auto float_type = floatbv_typet();
  float_type.set_width(32);
  float_type.set_f(23);
  auto expr =
    binary_exprt(f1.to_expr(), operator_type, f2.to_expr(), float_type);
  expr.type() = float_type;
  return simplify_expr(expr, ns);
}
}

TEST_CASE("Simplify plus floating_point expression")
{
  ieee_floatt result_f;
  result_f.from_float(12.0f);
  auto simplified = test_float_expr(ID_plus, 10.0f, 2.0f);
  REQUIRE(simplified == result_f.to_expr());
}

TEST_CASE("Simplify minus floating_point expression")
{
  ieee_floatt result_f;
  result_f.from_float(8.0f);
  auto simplified = test_float_expr(ID_minus, 10.0f, 2.0f);
  REQUIRE(simplified == result_f.to_expr());
}

TEST_CASE("Simplify mult floating_point expression")
{
  ieee_floatt result_f;
  result_f.from_float(20.0f);
  auto simplified = test_float_expr(ID_mult, 10.0f, 2.0f);
  REQUIRE(simplified == result_f.to_expr());
}

TEST_CASE("Simplify div floating_point expression")
{
  ieee_floatt result_f;
  result_f.from_float(5.0f);
  auto simplified = test_float_expr(ID_div, 10.0f, 2.0f);
  REQUIRE(simplified == result_f.to_expr());
}

TEST_CASE("Different rounding modes")
{
  floatbv_typet float_type;
  float_type.set_width(32);
  float_type.set_f(23);

  // slightly bigger than 0.1
  constant_exprt even_result("00111101110011001100110011001101", float_type);
  auto simplified_even =
    test_float_expr(ID_div, 1.0f, 10.0f, ieee_floatt::ROUND_TO_EVEN);
  CHECK(simplified_even == even_result);

  //slightly smaller than 0.1
  constant_exprt tozero_result("00111101110011001100110011001100", float_type);
  auto simplified_tozero =
    test_float_expr(ID_div, 1.0f, 10.0f, ieee_floatt::ROUND_TO_ZERO);
  CHECK(simplified_tozero == tozero_result);
}

TEST_CASE("Simplify pointer_offset(address of array index)")
{
  config.set_arch("none");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  array_typet array_type(char_type(), from_integer(2, size_type()));
  symbol_exprt array("A", array_type);
  index_exprt index(array, from_integer(1, index_type()));
  address_of_exprt address_of(index);

  exprt p_o=pointer_offset(address_of);

  exprt simp=simplify_expr(p_o, ns);

  REQUIRE(simp.id()==ID_constant);
  mp_integer offset_value;
  REQUIRE(!to_integer(simp, offset_value));
  REQUIRE(offset_value==1);
}

TEST_CASE("Simplify const pointer offset")
{
  config.set_arch("none");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  // build a numeric constant of some pointer type
  constant_exprt number=from_integer(1234, size_type());
  number.type()=pointer_type(char_type());

  exprt p_o=pointer_offset(number);

  exprt simp=simplify_expr(p_o, ns);

  REQUIRE(simp.id()==ID_constant);
  mp_integer offset_value;
  REQUIRE(!to_integer(simp, offset_value));
  REQUIRE(offset_value==1234);
}

namespace
{

void test_unnecessary_cast(const typet &type)
{
  config.set_arch("none");

  WHEN("The casts can be removed, they are")
  {
    const exprt simplified=simplify_expr(
      typecast_exprt(
        typecast_exprt(symbol_exprt("foo", type), java_int_type()),
        type),
      namespacet(symbol_tablet()));

    REQUIRE(simplified.id()==ID_symbol);
    REQUIRE(simplified.type()==type);
    const auto &symbol=to_symbol_expr(simplified);
    REQUIRE(symbol.get_identifier()=="foo");
  }

  WHEN("Casts should remain, they are left untouched")
  {
    {
      const exprt simplified=simplify_expr(
        typecast_exprt(symbol_exprt("foo", type), java_int_type()),
        namespacet(symbol_tablet()));

      REQUIRE(simplified.id()==ID_typecast);
      REQUIRE(simplified.type()==java_int_type());
    }

    {
      const exprt simplified=simplify_expr(
        typecast_exprt(symbol_exprt("foo", java_int_type()), type),
        namespacet(symbol_tablet()));

      REQUIRE(simplified.id()==ID_typecast);
      REQUIRE(simplified.type()==type);
    }
  }

  WHEN("Deeply nested casts are present, they are collapsed appropriately")
  {
    {
      const exprt simplified=simplify_expr(
        typecast_exprt(
          typecast_exprt(
            typecast_exprt(
              typecast_exprt(
                typecast_exprt(symbol_exprt("foo", type), java_int_type()),
                type),
              java_int_type()),
            type),
          java_int_type()),
        namespacet(symbol_tablet()));

      REQUIRE(
        simplified==typecast_exprt(symbol_exprt("foo", type), java_int_type()));
    }
  }
}

} // namespace

TEST_CASE("Simplify Java boolean -> int -> boolean casts")
{
  test_unnecessary_cast(java_boolean_type());
}

TEST_CASE("Simplify Java byte -> int -> byte casts")
{
  test_unnecessary_cast(java_byte_type());
}

TEST_CASE("Simplify Java char -> int -> char casts")
{
  test_unnecessary_cast(java_char_type());
}

TEST_CASE("Simplify Java short -> int -> short casts")
{
  test_unnecessary_cast(java_short_type());
}
