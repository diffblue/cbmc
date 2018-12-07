/*******************************************************************\

 Module: Unit tests for converting annotations

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>
#include <testing-utils/free_form_cmdline.h>
#include <testing-utils/message.h>
#include <util/options.h>

class test_java_bytecode_languaget : public java_bytecode_languaget
{
public:
  std::vector<irep_idt> get_parsed_class_names()
  {
    std::vector<irep_idt> parsed_class_names;
    for(const auto &named_class
      : java_class_loader.get_class_with_overlays_map())
    {
      parsed_class_names.push_back(named_class.first);
    }
    return parsed_class_names;
  }

  java_class_loadert::parse_tree_with_overlayst &get_parse_trees_for_class(
    const irep_idt &class_name)
  {
    return java_class_loader.get_class_with_overlays_map().at(class_name);
  }
};

static irep_idt get_base_name(const typet &type)
{
  return type.get(ID_C_base_name);
}

static void require_matching_annotations(
  const java_bytecode_parse_treet::annotationst &annotations,
  std::vector<irep_idt> expected_annotations)
{
  std::vector<irep_idt> annotation_names;
  std::transform(
    annotations.begin(),
    annotations.end(),
    std::back_inserter(annotation_names),
    [](const java_bytecode_parse_treet::annotationt &annotation)
    {
      return get_base_name(
        require_type::require_pointer(annotation.type, {}).subtype());
    });
  std::sort(annotation_names.begin(), annotation_names.end());
  std::sort(expected_annotations.begin(), expected_annotations.end());
  REQUIRE_THAT(
    annotation_names,
    Catch::Matchers::Equals(expected_annotations));
}

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
          id2string(to_struct_tag_type(java_type.subtype()).get_identifier());
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
    WHEN("Parsing a class with annotations everywhere")
    {
      free_form_cmdlinet command_line;
      command_line.add_flag("no-lazy-methods");
      command_line.add_flag("no-refine-strings");
      test_java_bytecode_languaget language;
      language.set_message_handler(null_message_handler);
      optionst options;
      parse_java_language_options(command_line, options);
      language.set_language_options(options);

      std::istringstream java_code_stream("ignored");
      language.parse(java_code_stream, "AnnotationsEverywhere.class");
      const java_class_loadert::parse_tree_with_overlayst &parse_trees =
        language.get_parse_trees_for_class("AnnotationsEverywhere");
      REQUIRE(parse_trees.size() == 1);
      const java_bytecode_parse_treet::classt &parsed_class =
        parse_trees.front().parsed_class;

      THEN("Only the correct annotations should be on the class")
      {
        require_matching_annotations(
          parsed_class.annotations,
          { "ClassAnnotation", "RuntimeClassAnnotation" });
      }

      THEN("Only the correct annotations should be on the field")
      {
        REQUIRE(parsed_class.fields.size() == 1);
        const java_bytecode_parse_treet::fieldt &field =
          parsed_class.fields.front();
        require_matching_annotations(
          field.annotations, { "FieldAnnotation", "RuntimeFieldAnnotation" });
      }

      auto method_it = std::find_if(
        parsed_class.methods.begin(),
        parsed_class.methods.end(),
        [](const java_bytecode_parse_treet::methodt &method)
        {
          return method.name == "foo";
        });
      REQUIRE(method_it != parsed_class.methods.end());
      const java_bytecode_parse_treet::methodt &method = *method_it;

      THEN("Only the correct annotations should be on the method")
      {
        require_matching_annotations(
          method.annotations,
          { "MethodAnnotation", "RuntimeMethodAnnotation" });
      }

      THEN("Only the correct annotations should be on the parameter")
      {
        REQUIRE(method.parameter_annotations.size() == 2);
        require_matching_annotations(
          method.parameter_annotations[0],
          { "RuntimeParameterAnnotation" });
        require_matching_annotations(
          method.parameter_annotations[1],
          { "ParameterAnnotation" });
      }
    }
  }
}
