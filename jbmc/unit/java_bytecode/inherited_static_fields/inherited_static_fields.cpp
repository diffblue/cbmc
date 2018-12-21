/*******************************************************************\

Module: Unit tests for inherited static fields

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>

#include <algorithm>

#include <java_bytecode/java_types.h>
#include <util/expr_iterator.h>

/// Check the full tree of expr for any symbol_exprts that have an identifier id
/// \param expr: expr to check
/// \param id: symbol id to look for
/// \return true if a suitable symbol_exprt is found
static bool contains_symbol_reference(const exprt &expr, const irep_idt &id)
{
  return std::any_of(
    expr.depth_begin(), expr.depth_end(), [id](const exprt &e) {
      return e.id() == ID_symbol && to_symbol_expr(e).get_identifier() == id;
    });
}

SCENARIO(
  "inherited_static_types", "[core][java_bytecode][inherited_static_types]")
{
  WHEN("A class uses an inherited static field 'x'")
  {
    symbol_tablet symbol_table=
      load_java_class("Test1", "./java_bytecode/inherited_static_fields");
    THEN("A static field 'Parent1.x' should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::Parent1.x"));
    }
    THEN("No static field 'Test1.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test1.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test1.main should refer to Parent1.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test1.main:()I").value,
          "java::Parent1.x"));
    }
  }

  WHEN("A class uses an interface static field 'x'")
  {
    symbol_tablet symbol_table=
      load_java_class("Test2", "./java_bytecode/inherited_static_fields");
    THEN("A static field 'StaticInterface2.x' should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::StaticInterface2.x"));
    }
    THEN("No static field 'Test2.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test2.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test2.main should refer to StaticInterface2.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test2.main:()I").value,
          "java::StaticInterface2.x"));
    }
  }

  WHEN("A class with an opaque parent uses an inherited static field 'x'")
  {
    symbol_tablet symbol_table=
      load_java_class("Test3", "./java_bytecode/inherited_static_fields");
    THEN("Type OpaqueParent3 should be opaque")
    {
      REQUIRE(
        to_java_class_type(symbol_table.lookup_ref("java::OpaqueParent3").type)
          .get_is_stub());
    }
    THEN("A static field 'OpaqueParent3.x' should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::OpaqueParent3.x"));
    }
    THEN("No static field 'Test3.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test3.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test3.main should refer to OpaqueParent3.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test3.main:()I").value,
          "java::OpaqueParent3.x"));
    }
  }

  WHEN("A class with an opaque interface uses an inherited static field 'x'")
  {
    symbol_tablet symbol_table =
      load_java_class("Test4", "./java_bytecode/inherited_static_fields");
    THEN("Type OpaqueInterface4 should be opaque")
    {
      REQUIRE(to_java_class_type(
                symbol_table.lookup_ref("java::OpaqueInterface4").type)
                .get_is_stub());
    }
    THEN("A static field 'OpaqueInterface4.x' should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::OpaqueInterface4.x"));
    }
    THEN("No static field 'Test4.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test4.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test4.main should refer to OpaqueInterface4.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test4.main:()I").value,
          "java::OpaqueInterface4.x"));
    }
  }

  WHEN("A class with two opaque parents uses an inherited static field 'x'")
  {
    symbol_tablet symbol_table=
      load_java_class("Test5", "./java_bytecode/inherited_static_fields");
    THEN("Type OpaqueParent5 should be opaque")
    {
      REQUIRE(
        to_java_class_type(symbol_table.lookup_ref("java::OpaqueParent5").type)
          .get_is_stub());
    }
    THEN("Type OpaqueInterface5 should be opaque")
    {
      REQUIRE(to_java_class_type(
                symbol_table.lookup_ref("java::OpaqueInterface5").type)
                .get_is_stub());
    }
    THEN("One or other parent (not both) should gain a static field 'x'")
    {
      REQUIRE(
        symbol_table.has_symbol("java::OpaqueInterface5.x") !=
        symbol_table.has_symbol("java::OpaqueParent5.x"));
    }
    THEN("No static field 'Test5.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test5.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test5.main should use either OpaqueParent5.x or OpaqueInterface5.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test5.main:()I").value,
          "java::OpaqueInterface5.x") !=
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test5.main:()I").value,
          "java::OpaqueParent5.x"));
    }
  }

  WHEN("A class refers to a parent's protected static field")
  {
    symbol_tablet symbol_table=
      load_java_class("Test6", "./java_bytecode/inherited_static_fields");
    THEN("A static field Parent6.x should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::Parent6.x"));
    }
    THEN("No static field 'Test6.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test6.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test6.main should use Parent6.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test6.main:()I").value,
          "java::Parent6.x"));
    }
  }

  WHEN("A class refers to an interface field "
       "and its parent has an invisible package-private field of the same name")
  {
    symbol_tablet symbol_table=
      load_java_class("Test7", "./java_bytecode/inherited_static_fields");
    THEN("A static field otherpackage.Parent7.x should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::otherpackage.Parent7.x"));
    }
    THEN("A static field StaticInterface7.x should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::StaticInterface7.x"));
    }
    THEN("No static field 'Test7.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test7.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test7.main should use StaticInterface7.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test7.main:()I").value,
          "java::StaticInterface7.x"));
    }
    THEN("Test7.main should not use otherpackage.Parent7.x")
    {
      REQUIRE(
        !contains_symbol_reference(
          symbol_table.lookup_ref("java::Test7.main:()I").value,
          "java::otherpackage.Parent7.x"));
    }
  }

  WHEN("A class refers to a parent's visible package-visibility field")
  {
    symbol_tablet symbol_table=
      load_java_class("Test8", "./java_bytecode/inherited_static_fields");
    THEN("A static field Parent8.x should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::Parent8.x"));
    }
    THEN("No static field 'Test8.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test8.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test8.main should use Parent8.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test8.main:()I").value,
          "java::Parent8.x"));
    }
  }

  WHEN("A class refers to an interface field "
       "and its parent has an invisible private field of the same name")
  {
    symbol_tablet symbol_table=
      load_java_class("Test9", "./java_bytecode/inherited_static_fields");
    THEN("A static field Parent9.x should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::Parent9.x"));
    }
    THEN("A static field StaticInterface9.x should exist")
    {
      REQUIRE(symbol_table.has_symbol("java::StaticInterface9.x"));
    }
    THEN("No static field 'Test9.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::Test9.x"));
    }
    THEN("No static field 'java.lang.Object.x' should be created")
    {
      REQUIRE(!symbol_table.has_symbol("java::java.lang.Object.x"));
    }
    THEN("Test9.main should use StaticInterface9.x")
    {
      REQUIRE(
        contains_symbol_reference(
          symbol_table.lookup_ref("java::Test9.main:()I").value,
          "java::StaticInterface9.x"));
    }
    THEN("Test9.main should not use Parent9.x")
    {
      REQUIRE(
        !contains_symbol_reference(
          symbol_table.lookup_ref("java::Test9.main:()I").value,
          "java::Parent9.x"));
    }
  }
}
