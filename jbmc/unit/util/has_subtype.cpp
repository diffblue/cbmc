/*******************************************************************\

 Module: Unit tests for has_subtype in expr_util.cpp

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <java_bytecode/java_types.h>

// Curryfied version of type comparison.
// Useful for the predicate argument of has_subtype
static std::function<bool(const typet &)> is_type(const typet &t1)
{
  auto f = [&](const typet &t2) { return t1 == t2; };
  return f;
}

SCENARIO("has_subtype", "[core][utils][has_subtype]")
{
  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  const typet char_type = java_char_type();
  const typet int_type = java_int_type();
  const typet bool_type = java_boolean_type();

  REQUIRE(has_subtype(char_type, is_type(char_type), ns));
  REQUIRE_FALSE(has_subtype(char_type, is_type(int_type), ns));

  GIVEN("a struct with char and int fields")
  {
    struct_typet struct_type;
    struct_type.components().emplace_back("char_field", char_type);
    struct_type.components().emplace_back("int_field", int_type);
    THEN("char and int are subtypes")
    {
      REQUIRE(has_subtype(struct_type, is_type(char_type), ns));
      REQUIRE(has_subtype(struct_type, is_type(int_type), ns));
    }
    THEN("bool is not a subtype")
    {
      REQUIRE_FALSE(has_subtype(struct_type, is_type(bool_type), ns));
    }
  }

  GIVEN("a pointer to char")
  {
    pointer_typet ptr_type = pointer_type(char_type);
    THEN("char is a subtype")
    {
      REQUIRE(has_subtype(ptr_type, is_type(char_type), ns));
    }
    THEN("int is not a subtype")
    {
      REQUIRE_FALSE(has_subtype(ptr_type, is_type(int_type), ns));
    }
  }

  GIVEN("a recursive struct definition")
  {
    struct_tag_typet struct_tag("A-struct");
    struct_typet::componentt comp("ptr", pointer_type(struct_tag));
    struct_typet struct_type;
    struct_type.components().push_back(comp);

    symbolt s;
    s.type = struct_type;
    s.name = "A-struct";
    s.is_type = true;
    symbol_table.add(s);

    THEN("has_subtype terminates")
    {
      REQUIRE_FALSE(
        has_subtype(struct_type, [&](const typet &) { return false; }, ns));
    }
    THEN("symbol type is a subtype")
    {
      REQUIRE(has_subtype(struct_type, is_type(pointer_type(struct_tag)), ns));
    }
    THEN("struct type is a subtype")
    {
      REQUIRE(has_subtype(struct_type, is_type(struct_type), ns));
    }
  }
}
