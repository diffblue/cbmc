/*******************************************************************\

 Module: Unit tests to parse a class without its methods' instructions

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_bytecode_parser.h>
#include <testing-utils/message.h>
#include <util/message.h>

#include <testing-utils/catch.hpp>

static void check_class_structure(
  const java_bytecode_parse_treet::classt &loaded_class)
{
  REQUIRE(loaded_class.methods.size() == 2);
  REQUIRE(loaded_class.is_public);
  REQUIRE(loaded_class.annotations.size() == 1);
  REQUIRE(loaded_class.fields.size() == 2);
  REQUIRE(loaded_class.super_class == "java.lang.Object");
  REQUIRE(loaded_class.is_inner_class);
  REQUIRE(loaded_class.outer_class == "Trivial");

  const auto &fieldone = *loaded_class.fields.begin();
  const auto &fieldtwo = *std::next(loaded_class.fields.begin());
  const auto &field_x = fieldone.name == "x" ? fieldone : fieldtwo;
  REQUIRE(field_x.name == "x");
  REQUIRE(field_x.is_private);
  REQUIRE(field_x.annotations.size() == 1);

  const auto &methodone = *loaded_class.methods.begin();
  const auto &methodtwo = *std::next(loaded_class.methods.begin());
  const auto &method_f =
    methodone.name == "f" ? methodone : methodtwo;
  const auto &method_constructor =
    methodone.name == "f" ? methodtwo : methodone;

  REQUIRE(method_f.is_public);
  REQUIRE(method_f.annotations.size() == 1);
  REQUIRE(method_constructor.is_public);
  REQUIRE(method_constructor.annotations.size() == 0);
}

SCENARIO(
  "java_bytecode_parse_class_without_instructions",
  "[core][java_bytecode][java_bytecode_parser]")
{
  WHEN("Loading a class without instructions")
  {
    auto loaded =
      java_bytecode_parse(
        "./java_bytecode/java_bytecode_parser/Trivial$Inner.class",
        null_message_handler,
        true);
    THEN("Loading should succeed")
    {
      REQUIRE(loaded);
      const auto &loaded_class = loaded->parsed_class;

      THEN("It should have the expected structure")
      {
        check_class_structure(loaded_class);
        const auto &methodone = *loaded_class.methods.begin();
        const auto &methodtwo = *std::next(loaded_class.methods.begin());

        THEN("Neither method should have instructions")
        {
          REQUIRE(methodone.instructions.size() == 0);
          REQUIRE(methodtwo.instructions.size() == 0);
        }
      }
    }
  }

  WHEN("Loading the same class normally")
  {
    auto loaded =
      java_bytecode_parse(
        "./java_bytecode/java_bytecode_parser/Trivial$Inner.class",
        null_message_handler,
        false);
    THEN("Loading should succeed")
    {
      REQUIRE(loaded);
      const auto &loaded_class = loaded->parsed_class;

      THEN("It should have the expected structure")
      {
        check_class_structure(loaded_class);
        const auto &methodone = *loaded_class.methods.begin();
        const auto &methodtwo = *std::next(loaded_class.methods.begin());

        THEN("Both methods should have instructions")
        {
          REQUIRE(methodone.instructions.size() != 0);
          REQUIRE(methodtwo.instructions.size() != 0);
        }
      }
    }
  }
}
