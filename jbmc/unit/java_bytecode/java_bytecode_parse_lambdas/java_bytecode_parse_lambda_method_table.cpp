/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <algorithm>
#include <functional>
#include <util/config.h>

#include <java-testing-utils/require_parse_tree.h>

#include <java_bytecode/java_bytecode_parser.h>
#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>

#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/run_test_with_compilers.h>

typedef java_bytecode_parse_treet::classt::lambda_method_handlet
  lambda_method_handlet;

SCENARIO(
  "lambda_method_handle_map with static lambdas",
  "[core][java_bytecode][java_bytecode_parse_lambda_method_handle]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    GIVEN(
      "A class with a static lambda variables from " + compiler + " compiler.")
    {
      optionalt<java_bytecode_parse_treet> parse_tree = java_bytecode_parse(
        "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
          compiler + "_classes/StaticLambdas.class",
        null_message_handler);
      WHEN("Parsing that class")
      {
        REQUIRE(parse_tree);
        REQUIRE(parse_tree->loading_successful);
        const java_bytecode_parse_treet::classt &parsed_class =
          parse_tree->parsed_class;
        REQUIRE(parsed_class.attribute_bootstrapmethods_read);
        REQUIRE(parsed_class.lambda_method_handle_map.size() == 12);

        // Simple lambdas
        THEN(
          "There should be an entry for the lambda that has no parameters or "
          "returns and the method it references should have an appropriate "
          "descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse" ? "StaticLambdas.lambda$0:()V"
                                  : "StaticLambdas.lambda$static$0:()V";
          const std::string method_type = "()V";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }

        // Parameter lambdas
        THEN(
          "There should be an entry for the lambda that takes parameters and "
          "the method it references should have an appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$1:(ILjava/lang/Object;LDummyGeneric;)V"
              : "StaticLambdas.lambda$static$1:(ILjava/lang/"
                "Object;LDummyGeneric;)V";
          const std::string method_type =
            "(ILjava/lang/Object;LDummyGeneric;)V";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }
        THEN(
          "There should be an entry for the lambda that takes array "
          "parameters and the method it references should have an appropriate "
          "descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$2:([I[Ljava/lang/Object;[LDummyGeneric;)V"
              : "StaticLambdas.lambda$static$2:([I[Ljava/lang/"
                "Object;[LDummyGeneric;)V";
          const std::string method_type =
            "([I[Ljava/lang/Object;[LDummyGeneric;)V";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }

        // Return lambdas
        THEN(
          "There should be an entry for the lambda that returns a primitive "
          "and the method it references should have an appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse" ? "StaticLambdas.lambda$3:()I"
                                  : "StaticLambdas.lambda$static$3:()I";
          const std::string method_type = "()I";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }
        THEN(
          "There should be an entry for the lambda that returns a reference "
          "type and the method it references should have an appropriate "
          "descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$4:()Ljava/lang/Object;"
              : "StaticLambdas.lambda$static$4:()Ljava/lang/Object;";
          const std::string method_type = "()Ljava/lang/Object;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }
        THEN(
          "There should be an entry for the lambda that returns a "
          "specialised generic type and the method it references should have "
          "an appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$5:()LDummyGeneric;"
              : "StaticLambdas.lambda$static$5:()LDummyGeneric;";
          const std::string method_type = "()LDummyGeneric;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }

        // Array returning lambdas
        THEN(
          "There should be an entry for the lambda that returns an array of "
          "primitives and the method it references should have an "
          "appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse" ? "StaticLambdas.lambda$6:()[I"
                                  : "StaticLambdas.lambda$static$6:()[I";
          const std::string method_type = "()[I";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }
        THEN(
          "There should be an entry for the lambda that returns an array of "
          "reference types and the method it references should have an "
          "appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$7:()[Ljava/lang/Object;"
              : "StaticLambdas.lambda$static$7:()[Ljava/lang/Object;";
          const std::string method_type = "()[Ljava/lang/Object;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }
        THEN(
          "There should be an entry for the lambda that returns an array of "
          "specialised generic types and the method it references should "
          "have an appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$8:()[LDummyGeneric;"
              : "StaticLambdas.lambda$static$8:()[LDummyGeneric;";
          const std::string method_type = "()[LDummyGeneric;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);
        }

        // Capturing lamdbas
        THEN(
          "There should be an entry for the lambda that returns a primitive "
          "and the method it references should have an appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse" ? "StaticLambdas.lambda$9:()I"
                                  : "StaticLambdas.lambda$static$9:()I";
          const std::string method_type = "()I";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);

          const typet primitive_type = java_int_type();

          fieldref_exprt fieldref{// NOLINT(whitespace/braces)
                                  primitive_type,
                                  "staticPrimitive",
                                  "StaticLambdas"};

          std::vector<require_parse_tree::expected_instructiont>
            expected_instructions{{"getstatic", {fieldref}}, {"ireturn", {}}};

          require_parse_tree::require_instructions_match_expectation(
            expected_instructions, lambda_method.instructions);
        }
        THEN(
          "There should be an entry for the lambda that returns a reference "
          "type and the method it references should have an appropriate "
          "descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$10:()Ljava/lang/Object;"
              : "StaticLambdas.lambda$static$10:()Ljava/lang/Object;";
          const std::string method_type = "()Ljava/lang/Object;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const auto lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);

          const reference_typet dummy_generic_reference_type =
            java_reference_type(struct_tag_typet{"java.lang.Object"});

          // NOLINTNEXTLINE(whitespace/braces)
          fieldref_exprt fieldref{
            dummy_generic_reference_type, "staticReference", "StaticLambdas"};

          std::vector<require_parse_tree::expected_instructiont>
            expected_instructions{{"getstatic", {fieldref}}, {"areturn", {}}};

          require_parse_tree::require_instructions_match_expectation(
            expected_instructions, lambda_method.instructions);
        }
        THEN(
          "There should be an entry for the lambda that returns a "
          "specialised generic type and the method it references should have "
          "an appropriate descriptor")
        {
          const std::string lambda_method_ref =
            compiler == "eclipse"
              ? "StaticLambdas.lambda$11:()LDummyGeneric;"
              : "StaticLambdas.lambda$static$11:()LDummyGeneric;";
          const std::string method_type = "()LDummyGeneric;";
          const lambda_method_handlet &lambda_entry =
            require_parse_tree::require_lambda_entry_for_descriptor(
              parsed_class, lambda_method_ref, method_type);

          const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

          const java_bytecode_parse_treet::methodt &lambda_method =
            require_parse_tree::require_method(parsed_class, lambda_impl_name);
          REQUIRE(id2string(lambda_method.descriptor) == method_type);

          const reference_typet dummy_generic_reference_type =
            java_reference_type(struct_tag_typet{"DummyGeneric"});

          fieldref_exprt fieldref{dummy_generic_reference_type,
                                  "staticSpecalisedGeneric",
                                  "StaticLambdas"};

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
      GIVEN("A method with local lambdas from " + compiler + " compiler.")
      {
        optionalt<java_bytecode_parse_treet> parse_tree = java_bytecode_parse(
          "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
            compiler + "_classes/LocalLambdas.class",
          null_message_handler);
        WHEN("Parsing that class")
        {
          REQUIRE(parse_tree);
          REQUIRE(parse_tree->loading_successful);
          const java_bytecode_parse_treet::classt &parsed_class =
            parse_tree->parsed_class;
          REQUIRE(parsed_class.attribute_bootstrapmethods_read);
          REQUIRE(parsed_class.lambda_method_handle_map.size() == 12);

          // Simple lambdas
          THEN(
            "There should be an entry for the lambda that has no parameters or "
            "returns and the method it references should have an appropriate "
            "descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "LocalLambdas.lambda$0:()V"
                                    : "LocalLambdas.lambda$test$0:()V";
            const std::string method_type = "()V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Parameter lambdas
          THEN(
            "There should be an entry for the lambda that takes parameters and "
            "the method it references should have an appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$1:(ILjava/lang/Object;LDummyGeneric;)V"
                : "LocalLambdas.lambda$test$1:(ILjava/lang/"
                  "Object;LDummyGeneric;)V";
            const std::string method_type =
              "(ILjava/lang/Object;LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that takes array "
            "parameters and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$2:([I[Ljava/lang/"
                  "Object;[LDummyGeneric;)V"
                : "LocalLambdas.lambda$test$2:([I[Ljava/lang/"
                  "Object;[LDummyGeneric;)V";
            const std::string method_type =
              "([I[Ljava/lang/Object;[LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Return lambdas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "and the method it references should have an appropriate "
            "descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "LocalLambdas.lambda$3:()I"
                                    : "LocalLambdas.lambda$test$3:()I";
            const std::string method_type = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type and the method it references should have an appropriate "
            "descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$4:()Ljava/lang/Object;"
                : "LocalLambdas.lambda$test$4:()Ljava/lang/Object;";
            const std::string method_type = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised generic type and the method it references should have "
            "an appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$5:()LDummyGeneric;"
                : "LocalLambdas.lambda$test$5:()LDummyGeneric;";
            const std::string method_type = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Array returning lambdas
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "primitives and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "LocalLambdas.lambda$6:()[I"
                                    : "LocalLambdas.lambda$test$6:()[I";
            const std::string method_type = "()[I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "reference types and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$7:()[Ljava/lang/Object;"
                : "LocalLambdas.lambda$test$7:()[Ljava/lang/Object;";
            const std::string method_type = "()[Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "specialised generic types and the method it references should "
            "have an appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$8:()[LDummyGeneric;"
                : "LocalLambdas.lambda$test$8:()[LDummyGeneric;";
            const std::string method_type = "()[LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Capturing lamdbas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "local variable and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "LocalLambdas.lambda$9:(I)I"
                                    : "LocalLambdas.lambda$test$9:(I)I";
            const std::string method_type = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

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
            "type local variable  and the method it references should have an "
            "appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$10:(Ljava/lang/Object;)Ljava/"
                  "lang/Object;"
                : "LocalLambdas.lambda$test$10:(Ljava/lang/Object;)Ljava/"
                  "lang/Object;";
            const std::string method_type = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

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
            "specialised generic type local variable  and the method it "
            "references should have an appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "LocalLambdas.lambda$11:(LDummyGeneric;)LDummyGeneric;"
                : "LocalLambdas.lambda$test$11:(LDummyGeneric;)LDummyGeneric;";
            const std::string method_type = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

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
      GIVEN(
        "A class that has lambdas as member variables from " + compiler +
        " compiler.")
      {
        optionalt<java_bytecode_parse_treet> parse_tree = java_bytecode_parse(
          "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
            compiler + "_classes/MemberLambdas.class",
          null_message_handler);
        WHEN("Parsing that class")
        {
          REQUIRE(parse_tree);
          REQUIRE(parse_tree->loading_successful);
          const java_bytecode_parse_treet::classt &parsed_class =
            parse_tree->parsed_class;
          REQUIRE(parsed_class.attribute_bootstrapmethods_read);
          REQUIRE(parsed_class.lambda_method_handle_map.size() == 12);

          // Simple lambdas
          THEN(
            "There should be an entry for the lambda that has no parameters or "
            "returns and the method it references should have an appropriate "
            "descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "MemberLambdas.lambda$0:()V"
                                    : "MemberLambdas.lambda$new$0:()V";
            const std::string method_type = "()V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Parameter lambdas
          THEN(
            "There should be an entry for the lambda that takes parameters and "
            "the method it references should have an appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$1:(ILjava/lang/Object;LDummyGeneric;)V"
                : "MemberLambdas.lambda$new$1:(ILjava/lang/"
                  "Object;LDummyGeneric;)V";
            const std::string method_type =
              "(ILjava/lang/Object;LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that takes array "
            "parameters and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "MemberLambdas.lambda$2:([I[Ljava/lang/"
                                      "Object;[LDummyGeneric;)V"
                                    : "MemberLambdas.lambda$new$2:([I[Ljava/"
                                      "lang/Object;[LDummyGeneric;)V";
            const std::string method_type =
              "([I[Ljava/lang/Object;[LDummyGeneric;)V";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Return lambdas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "and the method it references should have an appropriate "
            "descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "MemberLambdas.lambda$3:()I"
                                    : "MemberLambdas.lambda$new$3:()I";
            const std::string method_type = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type and the method it references should have an appropriate "
            "descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$4:()Ljava/lang/Object;"
                : "MemberLambdas.lambda$new$4:()Ljava/lang/Object;";
            const std::string method_type = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised generic type and the method it references should have "
            "an appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$5:()LDummyGeneric;"
                : "MemberLambdas.lambda$new$5:()LDummyGeneric;";
            const std::string method_type = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Array returning lambdas
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "primitives and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "MemberLambdas.lambda$6:()[I"
                                    : "MemberLambdas.lambda$new$6:()[I";
            const std::string method_type = "()[I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "reference types and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$7:()[Ljava/lang/Object;"
                : "MemberLambdas.lambda$new$7:()[Ljava/lang/Object;";
            const std::string method_type = "()[Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }
          THEN(
            "There should be an entry for the lambda that returns an array of "
            "specialised generic types and the method it references should "
            "have an appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$8:()[LDummyGeneric;"
                : "MemberLambdas.lambda$new$8:()[LDummyGeneric;";
            const std::string method_type = "()[LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == method_type);
          }

          // Capturing lamdbas
          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "local variable and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse" ? "MemberLambdas.lambda$9:()I"
                                    : "MemberLambdas.lambda$new$9:()I";
            const std::string method_type = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

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
                                                    "MemberLambdas"};

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {primitive_fieldref}},
                                    {"ireturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a reference "
            "type local variable  and the method it references should have an "
            "appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$10:()Ljava/lang/Object;"
                : "MemberLambdas.lambda$new$10:()Ljava/lang/Object;";
            const std::string method_type = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(
              id2string(lambda_method.descriptor) == "()Ljava/lang/Object;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(struct_tag_typet{"java.lang.Object"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt reference_fieldref{
              dummy_generic_reference_type, "memberReference", "MemberLambdas"};

            std::vector<require_parse_tree::expected_instructiont>
              expected_instructions{{"aload_0", {}}, // load this of stack
                                    {"getfield", {reference_fieldref}},
                                    {"areturn", {}}};

            require_parse_tree::require_instructions_match_expectation(
              expected_instructions, lambda_method.instructions);
          }
          THEN(
            "There should be an entry for the lambda that returns a "
            "specialised generic type local variable  and the method it "
            "references should have an appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "MemberLambdas.lambda$11:()LDummyGeneric;"
                : "MemberLambdas.lambda$new$11:()LDummyGeneric;";
            const std::string method_type = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const java_bytecode_parse_treet::methodt &lambda_method =
              require_parse_tree::require_method(
                parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == "()LDummyGeneric;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(struct_tag_typet{"DummyGeneric"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt generic_reference_fieldref{
              dummy_generic_reference_type,
              "memberSpecalisedGeneric",
              "MemberLambdas"};

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
      GIVEN(
        "An inner class with member variables as lambdas that capture outer "
        "variables from " +
        compiler + " compiler.")
      {
        optionalt<java_bytecode_parse_treet> parse_tree = java_bytecode_parse(
          "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
            compiler + "_classes/OuterMemberLambdas$Inner.class",
          null_message_handler);
        WHEN("Parsing that class")
        {
          REQUIRE(parse_tree);
          REQUIRE(parse_tree->loading_successful);
          const java_bytecode_parse_treet::classt &parsed_class =
            parse_tree->parsed_class;
          REQUIRE(parsed_class.attribute_bootstrapmethods_read);
          REQUIRE(parsed_class.lambda_method_handle_map.size() == 3);

          // Field ref for getting the outer class
          const reference_typet outer_class_reference_type =
            java_reference_type(struct_tag_typet{"OuterMemberLambdas"});
          // NOLINTNEXTLINE(whitespace/braces)
          const fieldref_exprt outer_fieldref{
            outer_class_reference_type, "this$0", "OuterMemberLambdas$Inner"};

          THEN(
            "There should be an entry for the lambda that returns a primitive "
            "local variable and the method it references should have an "
            "appropriate descriptor")
          {
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "OuterMemberLambdas$Inner.lambda$0:()I"
                : "OuterMemberLambdas$Inner.lambda$new$0:()I";
            const std::string method_type = "()I";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            // Note here the descriptor of the implementation is different - the
            // implementation requries the input to be passed in
            REQUIRE(id2string(lambda_method.descriptor) == "()I");
            REQUIRE_FALSE(lambda_method.is_static);

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt primitive_fieldref{
              java_int_type(), "memberPrimitive", "OuterMemberLambdas"};

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
            "type local variable  and the method it references should have an "
            "appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "OuterMemberLambdas$Inner.lambda$1:()Ljava/lang/Object;"
                : "OuterMemberLambdas$Inner.lambda$new$1:()Ljava/lang/Object;";
            const std::string method_type = "()Ljava/lang/Object;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const auto lambda_method = require_parse_tree::require_method(
              parsed_class, lambda_impl_name);
            REQUIRE(
              id2string(lambda_method.descriptor) == "()Ljava/lang/Object;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(struct_tag_typet{"java.lang.Object"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt reference_fieldref{
              dummy_generic_reference_type,
              "memberReference",
              "OuterMemberLambdas"};

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
            "specialised generic type local variable  and the method it "
            "references should have an appropriate descriptor")
          {
            // Since it is a local variable, the corresponding method takes the
            // captured variable as an input
            const std::string lambda_method_ref =
              compiler == "eclipse"
                ? "OuterMemberLambdas$Inner.lambda$2:()LDummyGeneric;"
                : "OuterMemberLambdas$Inner.lambda$new$2:()LDummyGeneric;";
            const std::string method_type = "()LDummyGeneric;";
            const lambda_method_handlet &lambda_entry =
              require_parse_tree::require_lambda_entry_for_descriptor(
                parsed_class, lambda_method_ref, method_type);

            const irep_idt &lambda_impl_name = lambda_entry.lambda_method_name;

            const java_bytecode_parse_treet::methodt &lambda_method =
              require_parse_tree::require_method(
                parsed_class, lambda_impl_name);
            REQUIRE(id2string(lambda_method.descriptor) == "()LDummyGeneric;");
            REQUIRE_FALSE(lambda_method.is_static);

            const reference_typet dummy_generic_reference_type =
              java_reference_type(struct_tag_typet{"DummyGeneric"});

            // NOLINTNEXTLINE(whitespace/braces)
            const fieldref_exprt generic_reference_fieldref{
              dummy_generic_reference_type,
              "memberSpecalisedGeneric",
              "OuterMemberLambdas"};

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
