/*******************************************************************\

 Module: Unit tests for converting annotations

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>

// See
// https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.7.16.1
SCENARIO(
  "java_bytecode_parse_annotations",
  "[core][java_bytecode][java_bytecode_parser]")
{
  GIVEN("Some class files in the class path")
  {
    WHEN(
      "Parsing an annotation with Class value specified to non-primitive "
      "(java.lang.String)")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "ClassWithClassTypeAnnotation", "./java_bytecode/java_bytecode_parser");

      THEN("The annotation should store the correct type (String)")
      {
        const symbolt &class_symbol =
          *new_symbol_table.lookup("java::ClassWithClassTypeAnnotation");
        const std::vector<java_annotationt> &java_annotations =
          to_annotated_type(class_symbol.type).get_annotations();
        java_bytecode_parse_treet::annotationst annotations;
        convert_java_annotations(java_annotations, annotations);
        REQUIRE(annotations.size() == 1);
        const auto &annotation = annotations.front();
        const auto &element_value_pair = annotation.element_value_pairs.front();
        const auto &id =
          to_symbol_expr(element_value_pair.value).get_identifier();
        const auto &java_type = java_type_from_string(id2string(id));
        const std::string &class_name =
          id2string(to_symbol_type(java_type.subtype()).get_identifier());
        REQUIRE(id2string(class_name) == "java::java.lang.String");
      }
    }
    WHEN("Parsing an annotation with Class value specified to primitive (byte)")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "ClassWithPrimitiveTypeAnnotation",
        "./java_bytecode/java_bytecode_parser");

      THEN("The annotation should store the correct type (byte)")
      {
        const symbolt &class_symbol =
          *new_symbol_table.lookup("java::ClassWithPrimitiveTypeAnnotation");
        const std::vector<java_annotationt> &java_annotations =
          to_annotated_type(class_symbol.type).get_annotations();
        java_bytecode_parse_treet::annotationst annotations;
        convert_java_annotations(java_annotations, annotations);
        REQUIRE(annotations.size() == 1);
        const auto &annotation = annotations.front();
        const auto &element_value_pair = annotation.element_value_pairs.front();
        const auto &id =
          to_symbol_expr(element_value_pair.value).get_identifier();
        const auto &java_type = java_type_from_string(id2string(id));
        REQUIRE(java_type == java_byte_type());
      }
    }
    WHEN("Parsing an annotation with Class value specified to void")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "ClassWithVoidTypeAnnotation", "./java_bytecode/java_bytecode_parser");

      THEN("The annotation should store the correct type (void)")
      {
        const symbolt &class_symbol =
          *new_symbol_table.lookup("java::ClassWithVoidTypeAnnotation");
        const std::vector<java_annotationt> &java_annotations =
          to_annotated_type(class_symbol.type).get_annotations();
        java_bytecode_parse_treet::annotationst annotations;
        convert_java_annotations(java_annotations, annotations);
        REQUIRE(annotations.size() == 1);
        const auto &annotation = annotations.front();
        const auto &element_value_pair = annotation.element_value_pairs.front();
        const auto &id =
          to_symbol_expr(element_value_pair.value).get_identifier();
        const auto &java_type = java_type_from_string(id2string(id));
        REQUIRE(java_type == void_type());
      }
    }
    WHEN("Parsing an annotation with an array field.")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "ClassWithArrayAnnotation", "./java_bytecode/java_bytecode_parser");

      THEN("The annotation should store an array of type string.")
      {
        const symbolt &class_symbol =
          *new_symbol_table.lookup("java::ClassWithArrayAnnotation");
        const std::vector<java_annotationt> &java_annotations =
          to_annotated_type(class_symbol.type).get_annotations();
        java_bytecode_parse_treet::annotationst annotations;
        convert_java_annotations(java_annotations, annotations);
        REQUIRE(annotations.size() == 1);
        const auto &annotation = annotations.front();
        const auto &element_value_pair = annotation.element_value_pairs.front();
        const auto &array = to_array_expr(element_value_pair.value);

        REQUIRE(array.operands().size() == 2);
        const auto &dave = array.op0().get(ID_value);
        const auto &another_dave = array.op1().get(ID_value);
        REQUIRE(id2string(dave) == "Dave");
        REQUIRE(id2string(another_dave) == "Another Dave");
      }
    }
  }
}
