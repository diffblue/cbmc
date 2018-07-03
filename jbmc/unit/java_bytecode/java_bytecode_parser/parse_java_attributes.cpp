/*******************************************************************\

 Module: Unit tests for converting annotations

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>

SCENARIO(
  "java_bytecode_parse_attributes",
  "[core][java_bytecode][java_bytecode_parser]")
{
  GIVEN("Some public class files in the class path with inner classes")
  {
    const symbol_tablet &new_symbol_table =
      load_java_class("InnerClasses", "./java_bytecode/java_bytecode_parser");
    WHEN("Parsing the InnerClasses attribute for a public inner class")
    {
      THEN("The class should be marked as public")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$PublicInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a package private inner class")
    {
      THEN("The class should be marked as default")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$DefaultInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a protected inner class")
    {
      THEN("The class should be marked as protected")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$ProtectedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a private inner class")
    {
      THEN("The class should be marked as private")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$PrivateInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
  }
  GIVEN("Some package-private class files in the class path with inner classes")
  {
    const symbol_tablet &new_symbol_table = load_java_class(
      "InnerClassesDefault", "./java_bytecode/java_bytecode_parser");
    WHEN("Parsing the InnerClasses attribute for a public inner class")
    {
      THEN("The class should be marked as public")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDefault$PublicInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a package private inner class")
    {
      THEN("The class should be marked as default")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDefault$DefaultInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a protected inner class")
    {
      THEN("The class should be marked as protected")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDefault$ProtectedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a private inner class")
    {
      THEN("The class should be marked as private")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDefault$PrivateInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
  }

  GIVEN(
    "Some package-private class files in the class path with deeply nested "
    "inner classes")
  {
    const symbol_tablet &new_symbol_table = load_java_class(
      "InnerClassesDeeplyNested", "./java_bytecode/java_bytecode_parser");
    WHEN(
      "Parsing the InnerClasses attribute for a public doubly-nested inner "
      "class")
    {
      THEN("The class should be marked as public")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "PublicDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package private doubly-nested "
      "inner class")
    {
      THEN("The class should be marked as default")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "DefaultDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a protected doubly-nested inner "
      "class")
    {
      THEN("The class should be marked as protected")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "ProtectedDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a private doubly-nested inner "
      "class")
    {
      THEN("The class should be marked as private")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "PrivateDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
  }

  GIVEN(
    "Some package-private class files in the class path with anonymous classes")
  {
    const symbol_tablet &new_symbol_table = load_java_class(
      "ContainsAnonymousClass", "./java_bytecode/java_bytecode_parser");
    WHEN("Parsing the InnerClasses attribute for a public anonymous class")
    {
      THEN("The class should be marked as public")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$1");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package-private anonymous "
      "class")
    {
      THEN("The class should be marked as default")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$2");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a protected anonymous class")
    {
      THEN("The class should be marked as protected")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$3");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
    WHEN("Parsing the InnerClasses attribute for a private anonymous class")
    {
      THEN("The class should be marked as private")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$4");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
  }

  GIVEN(
    "Some package-private class files in the class path with local classes ")
  {
    const symbol_tablet &new_symbol_table = load_java_class(
      "ContainsLocalClass", "./java_bytecode/java_bytecode_parser");
    WHEN("Parsing the InnerClasses attribute for a package-private class ")
    {
      THEN("The class should be marked as package-private")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsLocalClass$1LocalClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
      }
    }
  }
}
