/*******************************************************************\

 Module: Unit tests for has_subtype in
   solvers/refinement/string_refinement.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/c_types.h>
#include <solvers/refinement/string_refinement.h>
#include <java_bytecode/java_types.h>

// Curryfied version of type comparison.
// Useful for the predicate argument of has_subtype
static std::function<bool(const typet &)> is_type(const typet &t1)
{
  auto f = [&](const typet &t2) { return t1 == t2; };
  return f;
}

SCENARIO("has_subtype", "[core][solvers][refinement][string_refinement]")
{
  const typet char_type = java_char_type();
  const typet int_type = java_int_type();
  const typet bool_type = java_boolean_type();

  REQUIRE(has_subtype(char_type, is_type(char_type)));
  REQUIRE_FALSE(has_subtype(char_type, is_type(int_type)));

  GIVEN("a struct with char and int fields")
  {
    struct_typet struct_type;
    struct_type.components().emplace_back("char_field", char_type);
    struct_type.components().emplace_back("int_field", int_type);
    THEN("char and int are subtypes")
    {
      REQUIRE(has_subtype(struct_type, is_type(char_type)));
      REQUIRE(has_subtype(struct_type, is_type(int_type)));
    }
    THEN("bool is not a subtype")
    {
      REQUIRE_FALSE(has_subtype(struct_type, is_type(bool_type)));
    }
  }

  GIVEN("a pointer to char")
  {
    pointer_typet ptr_type = pointer_type(char_type);
    THEN("char is a subtype")
    {
      REQUIRE(has_subtype(ptr_type, is_type(char_type)));
    }
    THEN("int is not a subtype")
    {
      REQUIRE_FALSE(has_subtype(ptr_type, is_type(int_type)));
    }
  }
}
