/*******************************************************************\

Module: Unit tests of the expression simplifier

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/simplify_expr_class.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

TEST_CASE("Simplify pointer_offset(address of array index)", "[core][util]")
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
  const mp_integer offset_value =
    numeric_cast_v<mp_integer>(to_constant_expr(simp));
  REQUIRE(offset_value==1);
}

TEST_CASE("Simplify const pointer offset", "[core][util]")
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
  const mp_integer offset_value =
    numeric_cast_v<mp_integer>(to_constant_expr(simp));
  REQUIRE(offset_value==1234);
}

TEST_CASE("Simplify byte extract", "[core][util]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  // byte-extracting type T at offset 0 from an object of type T yields the
  // object
  symbol_exprt s("foo", size_type());
  byte_extract_exprt be(
    byte_extract_id(), s, from_integer(0, index_type()), size_type());

  exprt simp = simplify_expr(be, ns);

  REQUIRE(simp == s);
}

TEST_CASE("expr2bits and bits2expr respect bit order", "[core][util]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  simplify_exprt simp(ns);

  exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));

  const auto le = simp.expr2bits(deadbeef, true);
  REQUIRE(le.has_value());
  REQUIRE(le->size() == 32);

  const auto should_be_deadbeef1 =
    simp.bits2expr(*le, unsignedbv_typet(32), true);
  REQUIRE(deadbeef == *should_be_deadbeef1);

  const auto be = simp.expr2bits(deadbeef, false);
  REQUIRE(be.has_value());
  REQUIRE(be->size() == 32);

  const auto should_be_deadbeef2 =
    simp.bits2expr(*be, unsignedbv_typet(32), false);
  REQUIRE(deadbeef == *should_be_deadbeef2);
}

TEST_CASE("Simplify extractbit", "[core][util]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  const cmdlinet cmdline;
  config.set(cmdline);

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  // binary: 1101 1110 1010 1101 1011 1110 1110 1111
  //         ^MSB                               LSB^
  //              bit23^                  bit4^
  // extractbit and extractbits use offsets with respect to the
  // least-significant bit, endianess does not impact them
  const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));

  exprt eb1 = extractbit_exprt(deadbeef, 4);
  bool unmodified = simplify(eb1, ns);

  REQUIRE(!unmodified);
  REQUIRE(eb1 == false_exprt());

  exprt eb2 = extractbit_exprt(deadbeef, 23);
  unmodified = simplify(eb2, ns);

  REQUIRE(!unmodified);
  REQUIRE(eb2 == true_exprt());
}

TEST_CASE("Simplify extractbits", "[core][util]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  const cmdlinet cmdline;
  config.set(cmdline);

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));

  exprt eb = extractbits_exprt(deadbeef, 15, 8, unsignedbv_typet(8));
  bool unmodified = simplify(eb, ns);

  REQUIRE(!unmodified);
  REQUIRE(eb == from_integer(0xbe, unsignedbv_typet(8)));
}

TEST_CASE("Simplify shift", "[core][util]")
{
  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  REQUIRE(
    simplify_expr(shl_exprt(from_integer(5, signedbv_typet(8)), 1), ns) ==
    from_integer(10, signedbv_typet(8)));

  REQUIRE(
    simplify_expr(ashr_exprt(from_integer(5, signedbv_typet(8)), 1), ns) ==
    from_integer(2, signedbv_typet(8)));

  REQUIRE(
    simplify_expr(lshr_exprt(from_integer(5, unsignedbv_typet(8)), 1), ns) ==
    from_integer(2, unsignedbv_typet(8)));

  REQUIRE(
    simplify_expr(ashr_exprt(from_integer(-4, signedbv_typet(8)), 1), ns) ==
    from_integer(-2, signedbv_typet(8)));

  REQUIRE(
    simplify_expr(lshr_exprt(from_integer(-4, signedbv_typet(8)), 1), ns) ==
    from_integer(126, signedbv_typet(8)));
}

TEST_CASE("Simplify dynamic object comparison", "[core][util]")
{
  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  dynamic_object_exprt dynamic_object(signedbv_typet(8));
  dynamic_object.set_instance(1);

  address_of_exprt address_of_dynamic_object(dynamic_object);

  equal_exprt compare_null(
    address_of_dynamic_object,
    null_pointer_exprt(to_pointer_type(address_of_dynamic_object.type())));
  REQUIRE(simplify_expr(compare_null, ns) == false_exprt());

  typecast_exprt cast_address(
    address_of_dynamic_object, pointer_type(signedbv_typet(16)));

  equal_exprt compare_null_through_cast(
    cast_address, null_pointer_exprt(to_pointer_type(cast_address.type())));
  REQUIRE(simplify_expr(compare_null_through_cast, ns) == false_exprt());

  dynamic_object_exprt other_dynamic_object(signedbv_typet(8));
  other_dynamic_object.set_instance(2);
  address_of_exprt address_of_other_dynamic_object(other_dynamic_object);

  equal_exprt compare_pointer_objects(
    pointer_object(address_of_dynamic_object),
    pointer_object(address_of_other_dynamic_object));

  REQUIRE(simplify_expr(compare_pointer_objects, ns) == false_exprt());

  symbol_exprt s{"foo", signedbv_typet{8}};
  address_of_exprt address_of_symbol{s};

  equal_exprt compare_symbol_dynamic{address_of_dynamic_object,
                                     address_of_symbol};

  REQUIRE(simplify_expr(compare_symbol_dynamic, ns) == false_exprt{});
}

TEST_CASE("Simplify pointer_object equality", "[core][util]")
{
  // this test requires a proper architecture to be set up so that pointers have
  // a width
  const cmdlinet cmdline;
  config.set(cmdline);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  exprt p_o_void =
    pointer_object(null_pointer_exprt{pointer_type(empty_typet{})});
  exprt p_o_int =
    pointer_object(null_pointer_exprt{pointer_type(signedbv_typet(32))});

  exprt simp = simplify_expr(equal_exprt{p_o_void, p_o_int}, ns);

  REQUIRE(simp.is_true());
}

TEST_CASE("Simplify cast from bool", "[core][util]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  {
    // this checks that ((int)B)==1 turns into B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = equal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(1, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == B);
  }

  {
    // this checks that ((int)B)==0 turns into !B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = equal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(0, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == not_exprt(B));
  }

  {
    // this checks that ((int)B)!=1 turns into !B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = notequal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(1, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == not_exprt(B));
  }

  {
    // this checks that ((int)B)!=0 turns into B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = notequal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(0, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == B);
  }
}
