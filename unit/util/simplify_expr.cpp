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

SCENARIO("Comparing pointers to struct and union members")
{
  config.set_arch("none");
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  signedbv_typet int_type(32);

  // struct { int x; int y; } s;
  struct_typet simple_struct;
  simple_struct.components().emplace_back("x", int_type);
  simple_struct.components().emplace_back("y", int_type);

  symbol_exprt simple_struct_var("s", simple_struct);

  // union { int x; int y; } u;
  union_typet simple_union;
  simple_union.components().emplace_back("x", int_type);
  simple_union.components().emplace_back("y", int_type);

  symbol_exprt simple_union_var("u", simple_union);

  WHEN("Comparing pointers to the same member in a struct")
  {
    THEN("Equality should simplify to true")
    {
      // &s.x == &s.x
      auto x_equals_x = equal_exprt(
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)));
      REQUIRE(simplify_expr(x_equals_x, ns) == true_exprt());

      // &s.y == &s.y
      auto y_equals_y = equal_exprt(
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)));
      REQUIRE(simplify_expr(y_equals_y, ns) == true_exprt());
    }
    THEN("Inequality should simplify to false")
    {
      // &s.x != &s.x
      auto x_notequals_x = notequal_exprt(
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)));
      REQUIRE(simplify_expr(x_notequals_x, ns) == false_exprt());

      // &s.y != &s.y
      auto y_notequals_y = notequal_exprt(
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)));
      REQUIRE(simplify_expr(y_notequals_y, ns) == false_exprt());
    }
  }

  WHEN("Comparing pointers to different members in a struct")
  {
    THEN("Equality should simplify to false")
    {
      // &s.x == &s.y
      auto equals = equal_exprt(
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)));
      REQUIRE(simplify_expr(equals, ns) == false_exprt());
    }
    THEN("Inequality should simplify to true")
    {
      // &s.x != &s.y
      auto notequals = notequal_exprt(
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)));
      REQUIRE(simplify_expr(notequals, ns) == true_exprt());
    }
  }

  WHEN("Comparing pointer to struct with pointer to first member")
  {
    THEN("Equality should simplify to true")
    {
      // (int*)&s == &s.x
      auto equals = equal_exprt(
        typecast_exprt(
          address_of_exprt(simple_struct_var), pointer_type(int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)));
      REQUIRE(simplify_expr(equals, ns) == true_exprt());
    }

    THEN("Inequality should simplify to false")
    {
      // (int*)&s != &s.x
      auto notequals = notequal_exprt(
        typecast_exprt(
          address_of_exprt(simple_struct_var), pointer_type(int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "x", int_type)));
      REQUIRE(simplify_expr(notequals, ns) == false_exprt());
    }
  }

  WHEN("Comparing pointer to struct with pointer to member other than first")
  {
    THEN("Equality should simplify to false")
    {
      // (int*)&s == &s.y
      auto equals = equal_exprt(
        typecast_exprt(
          address_of_exprt(simple_struct_var), pointer_type(int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)));
      REQUIRE(simplify_expr(equals, ns) == false_exprt());
    }

    THEN("Inequality should simplify to true")
    {
      // (int*)&s != &s.y
      auto notequals = notequal_exprt(
        typecast_exprt(
          address_of_exprt(simple_struct_var), pointer_type(int_type)),
        address_of_exprt(member_exprt(simple_struct_var, "y", int_type)));
      REQUIRE(simplify_expr(notequals, ns) == true_exprt());
    }
  }

  WHEN("Comparing a pointers to the same union member")
  {
    THEN("Equality should simplify to true")
    {
      // &u.x == &u.x
      auto equals = equal_exprt(
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)));
      REQUIRE(simplify_expr(equals, ns) == true_exprt());
    }

    THEN("Inequality should simplify to false")
    {
      // &u.x != &u.x
      auto notequals = notequal_exprt(
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)));
      REQUIRE(simplify_expr(notequals, ns) == false_exprt());
    }
  }

  WHEN("Comparing pointers to different union members")
  {
    THEN("Equality should simplify to true")
    {
      // &u.x == &u.y
      auto equals = equal_exprt(
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_union_var, "y", int_type)));
      REQUIRE(simplify_expr(equals, ns) == true_exprt());
    }
    THEN("Inequality should simplify to false")
    {
      // &u.x != &u.y
      auto notequals = notequal_exprt(
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)),
        address_of_exprt(member_exprt(simple_union_var, "y", int_type)));
      REQUIRE(simplify_expr(notequals, ns) == false_exprt());
    }
  }

  WHEN("Comparing a pointer to union with a pointer to union member")
  {
    THEN("Equality should simplify to true")
    {
      // (int*)&u == &u.x
      auto equals = equal_exprt(
        typecast_exprt(
          address_of_exprt(simple_union_var), pointer_type(int_type)),
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)));
      REQUIRE(simplify_expr(equals, ns) == true_exprt());
    }
    THEN("Inequality should simplify to false")
    {
      // (int*)&u != &u.x
      auto notequals = notequal_exprt(
        typecast_exprt(
          address_of_exprt(simple_union_var), pointer_type(int_type)),
        address_of_exprt(member_exprt(simple_union_var, "x", int_type)));
      REQUIRE(simplify_expr(notequals, ns) == false_exprt());
    }
  }
}
