/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <algorithm>

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <testing-utils/run_test_with_compilers.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "Static lambdas in class symbol",
  "[core][java_bytecode][java_bytecode_convert_class_lambda_method_handles]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    GIVEN(
      "A class with static lambda variables from " + compiler + " compiler.")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "StaticLambdas",
        "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
          compiler + "_classes/");

      std::string class_prefix = "java::StaticLambdas";
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);

      THEN("The class has the correct list of lambda method handles")
      {
        std::vector<std::string> lambda_identifiers;
        if(compiler == "eclipse")
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::StaticLambdas.lambda$0:()V",
            "java::StaticLambdas.lambda$1:(ILjava/lang/Object;LDummyGeneric;)V",
            "java::StaticLambdas.lambda$2:([I[Ljava/lang/"
            "Object;[LDummyGeneric;)V",
            "java::StaticLambdas.lambda$3:()I",
            "java::StaticLambdas.lambda$4:()Ljava/lang/Object;",
            "java::StaticLambdas.lambda$5:()LDummyGeneric;",
            "java::StaticLambdas.lambda$6:()[I",
            "java::StaticLambdas.lambda$7:()[Ljava/lang/Object;",
            "java::StaticLambdas.lambda$8:()[LDummyGeneric;",
            "java::StaticLambdas.lambda$9:()I",
            "java::StaticLambdas.lambda$10:()Ljava/lang/Object;",
            "java::StaticLambdas.lambda$11:()LDummyGeneric;"};
        }
        else
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::StaticLambdas.lambda$static$0:()V",
            "java::StaticLambdas.lambda$static$1:(ILjava/lang/"
            "Object;LDummyGeneric;)V",
            "java::StaticLambdas.lambda$static$2:([I[Ljava/lang/"
            "Object;[LDummyGeneric;)V",
            "java::StaticLambdas.lambda$static$3:()I",
            "java::StaticLambdas.lambda$static$4:()Ljava/lang/Object;",
            "java::StaticLambdas.lambda$static$5:()LDummyGeneric;",
            "java::StaticLambdas.lambda$static$6:()[I",
            "java::StaticLambdas.lambda$static$7:()[Ljava/lang/Object;",
            "java::StaticLambdas.lambda$static$8:()[LDummyGeneric;",
            "java::StaticLambdas.lambda$static$9:()I",
            "java::StaticLambdas.lambda$static$10:()Ljava/lang/Object;",
            "java::StaticLambdas.lambda$static$11:()LDummyGeneric;"};
        }
        require_type::require_lambda_method_handles(
          to_java_class_type(class_symbol.type), lambda_identifiers);
      }
    }
  });
}

SCENARIO(
  "Local lambdas in class symbol",
  "[core][java_bytecode][java_bytecode_convert_class_lambda_method_handles]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    GIVEN(
      "A class with static lambda variables from " + compiler + " compiler.")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "LocalLambdas",
        "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
          compiler + "_classes/");

      std::string class_prefix = "java::LocalLambdas";
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);

      THEN("The class has the correct list of lambda method handles")
      {
        std::vector<std::string> lambda_identifiers;
        if(compiler == "eclipse")
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::LocalLambdas.lambda$0:()V",
            "java::LocalLambdas.lambda$1:(ILjava/lang/Object;"
            "LDummyGeneric;)V",
            "java::LocalLambdas.lambda$2:([I[Ljava/lang/Object;"
            "[LDummyGeneric;)V",
            "java::LocalLambdas.lambda$3:()I",
            "java::LocalLambdas.lambda$4:()Ljava/lang/Object;",
            "java::LocalLambdas.lambda$5:()LDummyGeneric;",
            "java::LocalLambdas.lambda$6:()[I",
            "java::LocalLambdas.lambda$7:()[Ljava/lang/Object;",
            "java::LocalLambdas.lambda$8:()[LDummyGeneric;",
            "java::LocalLambdas.lambda$9:(I)I",
            "java::LocalLambdas.lambda$10:(Ljava/lang/Object;)"
            "Ljava/lang/Object;",
            "java::LocalLambdas.lambda$11:(LDummyGeneric;)"
            "LDummyGeneric;"};
        }
        else
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::LocalLambdas.lambda$test$0:()V",
            "java::LocalLambdas.lambda$test$1:(ILjava/lang/Object;"
            "LDummyGeneric;)V",
            "java::LocalLambdas.lambda$test$2:([I[Ljava/lang/Object;"
            "[LDummyGeneric;)V",
            "java::LocalLambdas.lambda$test$3:()I",
            "java::LocalLambdas.lambda$test$4:()Ljava/lang/Object;",
            "java::LocalLambdas.lambda$test$5:()LDummyGeneric;",
            "java::LocalLambdas.lambda$test$6:()[I",
            "java::LocalLambdas.lambda$test$7:()[Ljava/lang/Object;",
            "java::LocalLambdas.lambda$test$8:()[LDummyGeneric;",
            "java::LocalLambdas.lambda$test$9:(I)I",
            "java::LocalLambdas.lambda$test$10:(Ljava/lang/Object;)"
            "Ljava/lang/Object;",
            "java::LocalLambdas.lambda$test$11:(LDummyGeneric;)"
            "LDummyGeneric;"};
        }
        require_type::require_lambda_method_handles(
          to_java_class_type(class_symbol.type), lambda_identifiers);
      }
    }
  });
}

SCENARIO(
  "Member lambdas in class symbol",
  "[core][java_bytecode][java_bytecode_convert_class_lambda_method_handles]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    GIVEN(
      "A class with static lambda variables from " + compiler + " compiler.")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "MemberLambdas",
        "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
          compiler + "_classes/");

      std::string class_prefix = "java::MemberLambdas";
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);

      THEN("The class has the correct list of lambda method handles")
      {
        std::vector<std::string> lambda_identifiers;
        if(compiler == "eclipse")
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::MemberLambdas.lambda$0:()V",
            "java::MemberLambdas.lambda$1:(ILjava/lang/Object;LDummyGeneric;)V",
            "java::MemberLambdas.lambda$2:([I[Ljava/lang/"
            "Object;[LDummyGeneric;)V",
            "java::MemberLambdas.lambda$3:()I",
            "java::MemberLambdas.lambda$4:()Ljava/lang/Object;",
            "java::MemberLambdas.lambda$5:()LDummyGeneric;",
            "java::MemberLambdas.lambda$6:()[I",
            "java::MemberLambdas.lambda$7:()[Ljava/lang/Object;",
            "java::MemberLambdas.lambda$8:()[LDummyGeneric;",
            "java::MemberLambdas.lambda$9:()I",
            "java::MemberLambdas.lambda$10:()Ljava/lang/Object;",
            "java::MemberLambdas.lambda$11:()LDummyGeneric;"};
        }
        else
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::MemberLambdas.lambda$new$0:()V",
            "java::MemberLambdas.lambda$new$1:(ILjava/lang/"
            "Object;LDummyGeneric;)V",
            "java::MemberLambdas.lambda$new$2:([I[Ljava/lang/"
            "Object;[LDummyGeneric;)V",
            "java::MemberLambdas.lambda$new$3:()I",
            "java::MemberLambdas.lambda$new$4:()Ljava/lang/Object;",
            "java::MemberLambdas.lambda$new$5:()LDummyGeneric;",
            "java::MemberLambdas.lambda$new$6:()[I",
            "java::MemberLambdas.lambda$new$7:()[Ljava/lang/Object;",
            "java::MemberLambdas.lambda$new$8:()[LDummyGeneric;",
            "java::MemberLambdas.lambda$new$9:()I",
            "java::MemberLambdas.lambda$new$10:()Ljava/lang/Object;",
            "java::MemberLambdas.lambda$new$11:()LDummyGeneric;"};
        }
        require_type::require_lambda_method_handles(
          to_java_class_type(class_symbol.type), lambda_identifiers);
      }
    }
  });
}

SCENARIO(
  "Member lambdas capturing outer class variables in class symbol",
  "[core][java_bytecode][java_bytecode_convert_class_lambda_method_handles]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    GIVEN(
      "A class with static lambda variables from " + compiler + " compiler.")
    {
      const symbol_tablet &new_symbol_table = load_java_class(
        "OuterMemberLambdas$Inner",
        "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/" +
          compiler + "_classes/");

      std::string class_prefix = "java::OuterMemberLambdas$Inner";
      REQUIRE(new_symbol_table.has_symbol(class_prefix));

      const symbolt &class_symbol = new_symbol_table.lookup_ref(class_prefix);

      THEN("The class has the correct list of lambda method handles")
      {
        std::vector<std::string> lambda_identifiers;
        if(compiler == "eclipse")
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::OuterMemberLambdas$Inner.lambda$0:()I",
            "java::OuterMemberLambdas$Inner.lambda$1:()Ljava/lang/Object;",
            "java::OuterMemberLambdas$Inner.lambda$2:()LDummyGeneric;"};
        }
        else
        {
          // NOLINTNEXTLINE(whitespace/braces)
          lambda_identifiers = {
            "java::OuterMemberLambdas$Inner.lambda$new$0:()I",
            "java::OuterMemberLambdas$Inner.lambda$new$1:()Ljava/lang/Object;",
            "java::OuterMemberLambdas$Inner.lambda$new$2:()LDummyGeneric;"};
        }
        require_type::require_lambda_method_handles(
          to_java_class_type(class_symbol.type), lambda_identifiers);
      }
    }
  });
}
