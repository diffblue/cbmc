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
  "java_bytecode_convert_annotations",
  "[core][java_bytecode][java_bytecode_convert_class]")
{
  GIVEN("Some class files in the class path")
  {
    WHEN("Parsing a class with class-level annotation MyClassAnnotation(6)")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "ClassWithClassAnnotation",
        "./java_bytecode/java_bytecode_convert_class");

      THEN("The annotation should have the correct structure")
      {
        const symbolt &class_symbol =
          *new_symbol_table.lookup("java::ClassWithClassAnnotation");
        const std::vector<java_annotationt> &java_annotations =
          to_annotated_type(class_symbol.type).get_annotations();
        java_bytecode_parse_treet::annotationst annotations;
        convert_java_annotations(java_annotations, annotations);
        REQUIRE(annotations.size() == 1);
        const auto &annotation = annotations.front();
        const auto &identifier =
          to_struct_tag_type(annotation.type.subtype()).get_identifier();
        REQUIRE(id2string(identifier) == "java::MyClassAnnotation");
        const auto &element_value_pair = annotation.element_value_pairs.front();
        const auto &element_name = element_value_pair.element_name;
        REQUIRE(id2string(element_name) == "value");
        const auto &expr = element_value_pair.value;
        const auto comp_expr = from_integer(6, java_int_type());
        REQUIRE(expr == comp_expr);
      }
    }
    WHEN("Parsing a class with method-level annotation MyMethodAnnotation(11)")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "ClassWithMethodAnnotation",
        "./java_bytecode/java_bytecode_convert_class");

      THEN("The annotation should have the correct structure")
      {
        const symbolt &method_symbol = *new_symbol_table.lookup(
          "java::ClassWithMethodAnnotation.myMethod:()V");
        const std::vector<java_annotationt> &java_annotations =
          to_annotated_type(method_symbol.type).get_annotations();
        java_bytecode_parse_treet::annotationst annotations;
        convert_java_annotations(java_annotations, annotations);
        REQUIRE(annotations.size() == 1);
        const auto &annotation = annotations.front();
        const auto &identifier =
          to_struct_tag_type(annotation.type.subtype()).get_identifier();
        REQUIRE(id2string(identifier) == "java::MyMethodAnnotation");
        const auto &element_value_pair = annotation.element_value_pairs.front();
        const auto &element_name = element_value_pair.element_name;
        REQUIRE(id2string(element_name) == "methodValue");
        const auto &expr = element_value_pair.value;
        const auto &comp_expr = from_integer(11, java_int_type());
        REQUIRE(expr == comp_expr);
      }
    }
  }
}
