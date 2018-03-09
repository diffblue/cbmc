/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: Diffblue Ltd.

\*******************************************************************/

#include <algorithm>
#include <functional>
#include <util/message.h>
#include <util/config.h>

#include <testing-utils/require_parse_tree.h>

#include <testing-utils/catch.hpp>
#include <java_bytecode/java_bytecode_parser.h>

#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>

typedef java_bytecode_parse_treet::classt::lambda_method_handlet
  lambda_method_handlet;

void run_test_with_compilers(
  const std::function<void(std::string)> &test_with_compiler)
{
  test_with_compiler("openjdk_8");
  test_with_compiler("eclipse");
  test_with_compiler("oracle_8");
  test_with_compiler("oracle_9");
}

SCENARIO(
  "lambda_method_handle_map with static lambdas",
  "[core][java_bytecode][java_bytecode_parse_lambda_method_handle]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    null_message_handlert message_handler;
    GIVEN(
      "A class with a static lambda variables from " + compiler + " compiler.")
    {
      java_bytecode_parse_treet parse_tree;
      java_bytecode_parse(
        "./java_bytecode/java_bytecode_parser/lambda_examples/" + compiler +
          "_classes/StaticLambdas.class",
        parse_tree,
        message_handler);
      WHEN("Parsing that class")
      {
        REQUIRE(parse_tree.loading_successful);
        const java_bytecode_parse_treet::classt parsed_class =
          parse_tree.parsed_class;
        REQUIRE(parsed_class.attribute_bootstrapmethods_read);
        REQUIRE(parsed_class.lambda_method_handle_map.size() == 12);

        // Simple lambdas
        THEN(
          "There should be an entry for the lambda that has no parameters or "
          "returns and the method it references should have an appropriate "
          "descriptor")
        {
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, "()V");

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == "()V");
        }

        // Parameter lambdas
        THEN(
          "There should be an entry for the lambda that takes parameters and "
          "the "
          "method it references should have an appropriate descriptor")
        {
          std::string descriptor = "(ILjava/lang/Object;LDummyGeneric;)V";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }
        THEN(
          "There should be an entry for the lambda that takes array "
          "parameters "
          "and the method it references should have an appropriate "
          "descriptor")
        {
          std::string descriptor = "([I[Ljava/lang/Object;[LDummyGeneric;)V";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }

        // Return lambdas
        THEN(
          "There should be an entry for the lambda that returns a primitive "
          "and "
          "the method it references should have an appropriate descriptor")
        {
          std::string descriptor = "()I";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }
        THEN(
          "There should be an entry for the lambda that returns a reference "
          "type "
          "and the method it references should have an appropriate "
          "descriptor")
        {
          std::string descriptor = "()Ljava/lang/Object;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }
        THEN(
          "There should be an entry for the lambda that returns a "
          "specialised "
          "generic type and the method it references should have an "
          "appropriate "
          "descriptor")
        {
          std::string descriptor = "()LDummyGeneric;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }

        // Array returning lambdas
        THEN(
          "There should be an entry for the lambda that returns an array of "
          "primitives and the method it references should have an "
          "appropriate "
          "descriptor")
        {
          std::string descriptor = "()[I";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }
        THEN(
          "There should be an entry for the lambda that returns an array of "
          "reference types and the method it references should have an "
          "appropriate descriptor")
        {
          std::string descriptor = "()[Ljava/lang/Object;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }
        THEN(
          "There should be an entry for the lambda that returns an array of "
          "specialised generic types and the method it references should "
          "have an "
          "appropriate descriptor")
        {
          std::string descriptor = "()[LDummyGeneric;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);
        }

        // Capturing lamdbas
        THEN(
          "There should be an entry for the lambda that returns a primitive "
          "and "
          "the method it references should have an appropriate descriptor")
        {
          std::string descriptor = "()I";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor, 1);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);

          const typet primitive_type = java_int_type();

          fieldref_exprt fieldref{// NOLINT(whitespace/braces)
                                  primitive_type,
                                  "staticPrimitive",
                                  "java::StaticLambdas"};

          std::vector<require_parse_tree::expected_instructiont>
            expected_instructions{{"getstatic", {fieldref}}, {"ireturn", {}}};

          require_parse_tree::require_instructions_match_expectation(
            expected_instructions, lambda_method.instructions);
        }
        THEN(
          "There should be an entry for the lambda that returns a reference "
          "type "
          "and the method it references should have an appropriate "
          "descriptor")
        {
          std::string descriptor = "()Ljava/lang/Object;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor, 1);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);

          const reference_typet dummy_generic_reference_type =
            java_reference_type(symbol_typet{"java::java.lang.Object"});

          fieldref_exprt fieldref{dummy_generic_reference_type,
                                  "staticReference",
                                  "java::StaticLambdas"};

          std::vector<require_parse_tree::expected_instructiont>
            expected_instructions{{"getstatic", {fieldref}}, {"areturn", {}}};

          require_parse_tree::require_instructions_match_expectation(
            expected_instructions, lambda_method.instructions);
        }
        THEN(
          "There should be an entry for the lambda that returns a "
          "specialised "
          "generic type and the method it references should have an "
          "appropriate "
          "descriptor")
        {
          std::string descriptor = "()LDummyGeneric;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, descriptor, 1);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const java_bytecode_parse_treet::methodt &lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == descriptor);

          const reference_typet dummy_generic_reference_type =
            java_reference_type(symbol_typet{"java::DummyGeneric"});

          fieldref_exprt fieldref{dummy_generic_reference_type,
                                  "staticSpecalisedGeneric",
                                  "java::StaticLambdas"};

          std::vector<require_parse_tree::expected_instructiont>
            expected_instructions{{"getstatic", {fieldref}}, {"areturn", {}}};

          require_parse_tree::require_instructions_match_expectation(
            expected_instructions, lambda_method.instructions);
        }
      }
    }
  });
}
SCENARIO(
  "lambda_method_handle_map with local lambdas",
  "[core][java_bytecode][java_bytecode_parse_lambda_method_handle]")
{
  run_test_with_compilers(
    [](const std::string &compiler) { // NOLINT(whitespace/braces)
      null_message_handlert message_handler;
      GIVEN("A method with local lambdas from " + compiler + " compiler.")
      {
        java_bytecode_parse_treet parse_tree;
        java_bytecode_parse(
          "./java_bytecode/java_bytecode_parser/lambda_examples/" + compiler +
            "_classes/LocalLambdas.class",
          parse_tree,
          message_handler);
        WHEN("Parsing that class")
        {
          REQUIRE(parse_tree.loading_successful);
          const java_bytecode_parse_treet::classt parsed_class =
            parse_tree.parsed_class;
          REQUIRE(parsed_class.attribute_bootstrapmethods_read);
          REQUIRE(parsed_class.lambda_method_handle_map.size() == 12);

          // Simple lambdas
          THEN(
            "There should be an entry for the lambda that has no parameters or "
            "returns and the method it references should have an appropriate "
            "descriptor")
          {
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, "()V");

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == "()V");
          }

          // Parameter lambdas
          THEN(
            "There should be an entry for the lambda that takes parameters and "
            "the "
            "method it references should have an appropriate descriptor")
          {
            std::string descriptor = "(ILjava/lang/Object;LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that takes array "
            "parameters "
            "and the method it references should have an appropriate "
            "descriptor")
          {
            std::string descriptor = "([I[Ljava/lang/Object;[LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }

          // Return lambdas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "and "
            "the method it references should have an appropriate descriptor")
          {
            std::string descriptor = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type "
            "and the method it references should have an appropriate "
            "descriptor")
          {
            std::string descriptor = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised "
            "generic type and the method it references should have an "
            "appropriate "
            "descriptor")
          {
            std::string descriptor = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }

          // Array returning lambdas
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "primitives and the method it references should have an "
            "appropriate "
            "descriptor")
          {
            std::string descriptor = "()[I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "reference types and the method it references should have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()[Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "specialised generic types and the method it references should "
            "have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()[LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }

          // Capturing lamdbas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "local variable and the method it references should have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor, 1);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            // Note here the descriptor of the implementation is different - the
            // implementation requries the input to be passed in
            REQUIRE(id2string(lambda_method.descriptor) == "(I)I");

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"iload_0", {}}, {"ireturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type "
            "local variable  and the method it references should have an "
            "appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            std::string descriptor = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor, 1);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(
              id2string(lambda_method.descriptor) ==
              "(Ljava/lang/Object;)Ljava/lang/Object;");

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised "
            "generic type local variable  and the method it references should "
            "have "
            "an appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            std::string descriptor = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor, 1);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const java_bytecode_parse_treet::methodt &lambda_method =
              require_parse_tree::require_method(
                parsed_class, lambda_impl_name);
            REQUIRE(
              id2string(lambda_method.descriptor) ==
              "(LDummyGeneric;)LDummyGeneric;");

            // since just returning the parameter, nothing to put on the stack
            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
        }
      }
    });
}
SCENARIO(
  "lambda_method_handle_map with member lambdas",
  "[core][java_bytecode][java_bytecode_parse_lambda_method_handle]")
{
  run_test_with_compilers(
    [](const std::string &compiler) { // NOLINT(whitespace/braces)
      null_message_handlert message_handler;
      GIVEN(
        "A class that has lambdas as member variables from " + compiler +
        " compiler.")
      {
        java_bytecode_parse_treet parse_tree;
        java_bytecode_parse(
          "./java_bytecode/java_bytecode_parser/lambda_examples/" + compiler +
            "_classes/MemberLambdas.class",
          parse_tree,
          message_handler);
        WHEN("Parsing that class")
        {
          REQUIRE(parse_tree.loading_successful);
          const java_bytecode_parse_treet::classt parsed_class =
            parse_tree.parsed_class;
          REQUIRE(parsed_class.attribute_bootstrapmethods_read);
          REQUIRE(parsed_class.lambda_method_handle_map.size() == 12);

          // Simple lambdas
          THEN(
            "There should be an entry for the lambda that has no parameters or "
            "returns and the method it references should have an appropriate "
            "descriptor")
          {
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, "()V");

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == "()V");
          }

          // Parameter lambdas
          THEN(
            "There should be an entry for the lambda that takes parameters and "
            "the "
            "method it references should have an appropriate descriptor")
          {
            std::string descriptor = "(ILjava/lang/Object;LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that takes array "
            "parameters "
            "and the method it references should have an appropriate "
            "descriptor")
          {
            std::string descriptor = "([I[Ljava/lang/Object;[LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }

          // Return lambdas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "and "
            "the method it references should have an appropriate descriptor")
          {
            std::string descriptor = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type "
            "and the method it references should have an appropriate "
            "descriptor")
          {
            std::string descriptor = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised "
            "generic type and the method it references should have an "
            "appropriate "
            "descriptor")
          {
            std::string descriptor = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }

          // Array returning lambdas
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "primitives and the method it references should have an "
            "appropriate "
            "descriptor")
          {
            std::string descriptor = "()[I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "reference types and the method it references should have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()[Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "specialised generic types and the method it references should "
            "have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()[LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == descriptor);
          }

          // Capturing lamdbas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "local variable and the method it references should have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor, 1);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            // Note here the descriptor of the implementation is different - the
            // implementation requries the input to be passed in
            REQUIRE(id2string(lambda_method.descriptor) == "()I");
            REQUIRE_FALSE(lambda_method.is_static);

            const fieldref_exprt primitive_fieldref{// NOLINT(whitespace/braces)
                                                    java_int_type(),
                                                    "memberPrimitive",
                                                    "java::MemberLambdas"};

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {primitive_fieldref}},
                                    {"ireturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type "
            "local variable  and the method it references should have an "
            "appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            std::string descriptor = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor, 1);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(
              id2string(lambda_method.descriptor) == "()Ljava/lang/Object;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(symbol_typet{"java::java.lang.Object"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt reference_fieldref{
              dummy_generic_reference_type,
              "memberReference",
              "java::MemberLambdas"};

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {reference_fieldref}},
                                    {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised "
            "generic type local variable  and the method it references should "
            "have "
            "an appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            std::string descriptor = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor, 1);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const java_bytecode_parse_treet::methodt &lambda_method =
              require_parse_tree::require_method(
                parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == "()LDummyGeneric;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(symbol_typet{"java::DummyGeneric"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt generic_reference_fieldref{
              dummy_generic_reference_type,
              "memberSpecalisedGeneric",
              "java::MemberLambdas"};

            // since just returning the parameter, nothing to put on the stack
            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {generic_reference_fieldref}},
                                    {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
        }
      }
    });
}
SCENARIO(
  "lambda_method_handle_map with member lambdas capturing outer class "
  "variables",
  "[core][java_bytecode][java_bytecode_parse_lambda_method_handle]")
{
  run_test_with_compilers(
    [](const std::string &compiler) { // NOLINT(whitespace/braces)
      null_message_handlert message_handler;
      GIVEN(
        "An inner class with member variables as lambdas that capture outer "
        "variables from " +
        compiler + " compiler.")
      {
        java_bytecode_parse_treet parse_tree;
        java_bytecode_parse(
          "./java_bytecode/java_bytecode_parser/lambda_examples/" + compiler +
            "_classes/OuterMemberLambdas$Inner.class",
          parse_tree,
          message_handler);
        WHEN("Parsing that class")
        {
          REQUIRE(parse_tree.loading_successful);
          const java_bytecode_parse_treet::classt parsed_class =
            parse_tree.parsed_class;
          REQUIRE(parsed_class.attribute_bootstrapmethods_read);
          REQUIRE(parsed_class.lambda_method_handle_map.size() == 3);

          // Field ref for getting the outer class
          const reference_typet outer_class_reference_type =
            java_reference_type(symbol_typet{"java::OuterMemberLambdas"});
          const fieldref_exprt outer_fieldref{outer_class_reference_type,
                                              "this$0",
                                              "java::OuterMemberLambdas$Inner"};

          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "local variable and the method it references should have an "
            "appropriate descriptor")
          {
            std::string descriptor = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            // Note here the descriptor of the implementation is different - the
            // implementation requries the input to be passed in
            REQUIRE(id2string(lambda_method.descriptor) == "()I");
            REQUIRE_FALSE(lambda_method.is_static);

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt primitive_fieldref{
              java_int_type(), "memberPrimitive", "java::OuterMemberLambdas"};

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {outer_fieldref}},
                                    {"getfield", {primitive_fieldref}},
                                    {"ireturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type "
            "local variable  and the method it references should have an "
            "appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            std::string descriptor = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(
              id2string(lambda_method.descriptor) == "()Ljava/lang/Object;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(symbol_typet{"java::java.lang.Object"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt reference_fieldref{
              dummy_generic_reference_type,
              "memberReference",
              "java::OuterMemberLambdas"};

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {outer_fieldref}},
                                    {"getfield", {reference_fieldref}},
                                    {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised "
            "generic type local variable  and the method it references should "
            "have "
            "an appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            std::string descriptor = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, descriptor);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const java_bytecode_parse_treet::methodt &lambda_method =
              require_parse_tree::require_method(
                parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == "()LDummyGeneric;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(symbol_typet{"java::DummyGeneric"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt generic_reference_fieldref{
              dummy_generic_reference_type,
              "memberSpecalisedGeneric",
              "java::OuterMemberLambdas"};

            // since just returning the parameter, nothing to put on the stack
            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {outer_fieldref}},
                                    {"getfield", {generic_reference_fieldref}},
                                    {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
        }
      }
    });
}
