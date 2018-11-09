/*******************************************************************\

Module: Unit tests for converting annotations

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_bytecode_convert_method.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/use_catch.h>

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
      THEN("The inner class should be marked as public")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$PublicInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
        REQUIRE(id2string(java_class.get_outer_class()) == "InnerClasses");
      }
    }
    WHEN("Parsing the InnerClasses attribute for a package private inner class")
    {
      THEN("The inner class should be marked as default")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$DefaultInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
        REQUIRE(id2string(java_class.get_outer_class()) == "InnerClasses");
      }
    }
    WHEN("Parsing the InnerClasses attribute for a protected inner class")
    {
      THEN("The inner class should be marked as protected")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$ProtectedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
        REQUIRE(id2string(java_class.get_outer_class()) == "InnerClasses");
      }
    }
    WHEN("Parsing the InnerClasses attribute for a private inner class")
    {
      THEN("The inner class should be marked as private")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::InnerClasses$PrivateInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(id2string(java_class.get_outer_class()) == "InnerClasses");
      }
    }
  }
  GIVEN(
    "Some package-private (default) class files in the class path with inner "
    "classes")
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
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
        REQUIRE(
          id2string(java_class.get_outer_class()) == "InnerClassesDefault");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package private (default) "
      "inner class")
    {
      THEN("The inner class should be marked as package-private (default)")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDefault$DefaultInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
        REQUIRE(
          id2string(java_class.get_outer_class()) == "InnerClassesDefault");
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
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
        REQUIRE(
          id2string(java_class.get_outer_class()) == "InnerClassesDefault");
      }
    }
    WHEN("Parsing the InnerClasses attribute for a private inner class")
    {
      THEN("The inner class should be marked as private")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDefault$PrivateInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(
          id2string(java_class.get_outer_class()) == "InnerClassesDefault");
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
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerClassesDeeplyNested$SinglyNestedClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package private (default) "
      "doubly-nested inner class")
    {
      THEN("The inner class should be marked as package-private (default)")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "DefaultDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerClassesDeeplyNested$SinglyNestedClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package private (default) "
      "doubly-nested inner class ")
    {
      THEN("The inner class should be marked as protected")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "ProtectedDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerClassesDeeplyNested$SinglyNestedClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a private doubly-nested inner "
      "class")
    {
      THEN("The inner class should be marked as private ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerClassesDeeplyNested$SinglyNestedClass$"
          "PrivateDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerClassesDeeplyNested$SinglyNestedClass");
      }
    }
  }

  GIVEN(
    "Some package-private class files in the class path with private deeply"
    "nested inner classes")
  {
    const symbol_tablet &new_symbol_table = load_java_class(
      "InnerPrivateClassesDeeplyNested",
      "./java_bytecode/java_bytecode_parser");
    WHEN(
      "Parsing the InnerClasses attribute for a public doubly-nested inner "
      "class")
    {
      THEN(
        "The inner class should be marked as private because its containing "
        "class has stricter access ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass$"
          "PublicDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package private doubly-nested "
      "inner class")
    {
      THEN(
        "The inner class should be marked as private because its containing "
        "class has stricter access ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass$"
          "DefaultDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a protected doubly-nested inner "
      "class")
    {
      THEN(
        "The inner class should be marked as private because its containing "
        "class has stricter access ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass$"
          "ProtectedDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a private doubly-nested inner "
      "class")
    {
      THEN("The inner class should be marked as private ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass$"
          "PrivateDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "InnerPrivateClassesDeeplyNested$SinglyNestedPrivateClass");
      }
    }
  }

  GIVEN(
    "Some class files where the outer class is more restrictive than the first "
    "inner class")
  {
    const symbol_tablet &new_symbol_table = load_java_class(
      "OuterClassMostRestrictiveDeeplyNested",
      "./java_bytecode/java_bytecode_parser");
    WHEN(
      "Parsing the InnerClasses attribute for a public doubly-nested inner "
      "class")
    {
      THEN(
        "The inner class should be marked as default (package-private) because "
        "one of its containing classes has stricter access ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass$"
          "PublicDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_public);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package private doubly-nested "
      "inner class")
    {
      THEN(
        "The inner class should be marked as default (package-private) because "
        "one of its containing classes has stricter access ")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass$"
          "DefaultDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_default);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a protected doubly-nested inner "
      "class")
    {
      THEN("The inner class should be marked as default (package-private)")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass$"
          "ProtectedDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_protected);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass");
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a private doubly-nested inner "
      "class")
    {
      THEN("The inner class should be marked as private")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass$"
          "PrivateDoublyNestedInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(
          id2string(java_class.get_outer_class()) ==
          "OuterClassMostRestrictiveDeeplyNested$SinglyNestedPublicClass");
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
      THEN("The class should be marked as private and anonymous")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$1");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a package-private anonymous "
      "class")
    {
      THEN("The class should be marked as private and anonymous")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$2");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
    WHEN("Parsing the InnerClasses attribute for a protected anonymous class")
    {
      THEN("The class should be marked as private and anonymous")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$3");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
    WHEN("Parsing the InnerClasses attribute for a private anonymous class")
    {
      THEN("The class should be marked as private and anonymous")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ContainsAnonymousClass$4");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_access() == ID_private);
        REQUIRE(java_class.get_outer_class().empty());
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
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
  }

  const symbol_tablet &new_symbol_table =
    load_java_class("StaticInnerClass", "./java_bytecode/java_bytecode_parser");
  GIVEN("Some class with a static inner class")
  {
    WHEN("Parsing the InnerClasses attribute for a static inner class ")
    {
      THEN("The class should be marked as static")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::StaticInnerClass$PublicStaticInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_static_class());
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(id2string(java_class.get_outer_class()) == "StaticInnerClass");
      }
    }
    WHEN("Parsing the InnerClasses attribute for a non-static inner class ")
    {
      THEN("The class should not be marked as static")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::StaticInnerClass$PublicNonStaticInnerClass");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE_FALSE(java_class.get_is_static_class());
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(id2string(java_class.get_outer_class()) == "StaticInnerClass");
      }
    }
  }
  GIVEN("Some class with a static anonymous class")
  {
    WHEN("Parsing the InnerClasses attribute for a static anonymous class ")
    {
      THEN("The class should be marked as static and anonymous")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::StaticInnerClass$1");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_is_static_class());
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
    WHEN("Parsing the InnerClasses attribute for a non-static anonymous class ")
    {
      THEN("The class should be marked as anonymous and not static")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::StaticInnerClass$2");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE(java_class.get_is_anonymous_class());
        REQUIRE_FALSE(java_class.get_is_static_class());
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
  }
  GIVEN("Some method containing a local class")
  {
    WHEN(
      "Parsing the InnerClasses attribute for a local class in a static "
      "method ")
    {
      THEN("The local class should be marked as static")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::StaticInnerClass$1LocalClassInStatic");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE_FALSE(java_class.get_is_static_class());
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
    WHEN(
      "Parsing the InnerClasses attribute for a local class in a non-static "
      "method ")
    {
      THEN("The local class should not be marked as static")
      {
        const symbolt &class_symbol = new_symbol_table.lookup_ref(
          "java::StaticInnerClass$1LocalClassInNonStatic");
        const java_class_typet java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_is_inner_class());
        REQUIRE_FALSE(java_class.get_is_static_class());
        REQUIRE_FALSE(java_class.get_is_anonymous_class());
        REQUIRE(java_class.get_outer_class().empty());
      }
    }
  }

  GIVEN("A method that may or may not throw exceptions")
  {
    const symbol_tablet &new_symbol_table2 = load_java_class(
      "ThrowsExceptions", "./java_bytecode/java_bytecode_parser");
    WHEN("Parsing the exceptions attribute for a method that throws exceptions")
    {
      THEN("We should be able to get the list of exceptions it throws")
      {
        const symbolt &method_symbol =
          new_symbol_table2.lookup_ref("java::ThrowsExceptions.test:()V");
        const java_method_typet method =
          to_java_method_type(method_symbol.type);
        const std::vector<irep_idt> exceptions = method.throws_exceptions();
        REQUIRE(exceptions.size() == 2);
        REQUIRE(
          std::find(
            exceptions.begin(),
            exceptions.end(),
            irept("CustomException").id()) != exceptions.end());
        REQUIRE(
          std::find(
            exceptions.begin(),
            exceptions.end(),
            irept("java.io.IOException").id()) != exceptions.end());
      }
    }
    WHEN(
      "Parsing the exceptions attribute for a method that throws no exceptions")
    {
      THEN("We should be able to get the list of exceptions it throws")
      {
        const symbolt &method_symbol = new_symbol_table2.lookup_ref(
          "java::ThrowsExceptions.testNoExceptions:()V");
        const java_method_typet method =
          to_java_method_type(method_symbol.type);
        const std::vector<irep_idt> exceptions = method.throws_exceptions();
        REQUIRE(exceptions.size() == 0);
      }
    }
  }
}
