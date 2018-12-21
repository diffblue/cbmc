/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <testing-utils/require_symbol.h>

SCENARIO(
  "Lazy load lambda methods",
  "[core][java_bytecode][ci_lazy_methods][lambdas][!mayfail]")
{
  GIVEN("A class with some locally declared lambdas")
  {
    const symbol_tablet symbol_table = load_java_class_lazy(
      "LocalLambdas",
      "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/"
      "openjdk_8_classes",
      "LocalLambdas.test");

    THEN("Then the lambdas should be loaded")
    {
      std::string lambda_name_prefix = "java::LocalLambdas.lambda$test$";
      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "0:()V");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "1:(ILjava/lang/Object;LDummyGeneric;)V");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "2:([I[Ljava/lang/Object;[LDummyGeneric;)V");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "3:()I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "4:()Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "5:()LDummyGeneric;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "6:()[I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "7:()[Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "8:()[LDummyGeneric;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "9:(I)I");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "10:(Ljava/lang/Object;)Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "11:(LDummyGeneric;)LDummyGeneric;");
    }
  }
  GIVEN("A class with some member lambdas")
  {
    const symbol_tablet symbol_table = load_java_class_lazy(
      "MemberLambdas",
      "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/"
      "openjdk_8_classes",
      "MemberLambdas.test");

    THEN("Then the lambdas should be loaded")
    {
      std::string lambda_name_prefix = "java::MemberLambdas.lambda$new$";
      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "0:()V");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "1:(ILjava/lang/Object;LDummyGeneric;)V");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "2:([I[Ljava/lang/Object;[LDummyGeneric;)V");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "3:()I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "4:()Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "5:()LDummyGeneric;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "6:()[I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "7:()[Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "8:()[LDummyGeneric;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "9:()I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "10:()Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "11:()LDummyGeneric;");
    }
  }
  GIVEN("A class with some static lambdas")
  {
    const symbol_tablet symbol_table = load_java_class_lazy(
      "StaticLambdas",
      "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/"
      "openjdk_8_classes",
      "StaticLambdas.test");

    THEN("Then the lambdas should be loaded")
    {
      std::string lambda_name_prefix = "java::StaticLambdas.lambda$static$";
      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "0:()V");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "1:(ILjava/lang/Object;LDummyGeneric;)V");

      require_symbol::require_symbol_exists(
        symbol_table,
        lambda_name_prefix + "2:([I[Ljava/lang/Object;[LDummyGeneric;)V");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "3:()I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "4:()Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "5:()LDummyGeneric;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "6:()[I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "7:()[Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "8:()[LDummyGeneric;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "9:()I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "10:()Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "11:()LDummyGeneric;");
    }
  }
  GIVEN("A class with some outer member lambdas")
  {
    const symbol_tablet symbol_table = load_java_class_lazy(
      "OuterMemberLambdas$Inner",
      "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/"
      "openjdk_8_classes",
      "OuterMemberLambdas$Inner.test");

    THEN("Then the lambdas should be loaded")
    {
      std::string lambda_name_prefix =
        "java::OuterMemberLambdas$Inner.lambda$new$";

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "0:()I");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "1:()Ljava/lang/Object;");

      require_symbol::require_symbol_exists(
        symbol_table, lambda_name_prefix + "2:()LDummyGeneric;");
    }
  }
}

SCENARIO(
  "Lazy load lambda methods in seperate class",
  "[core][java_bytecode][ci_lazy_methods][lambdas][!mayfail]")
{
  const symbol_tablet symbol_table = load_java_class_lazy(
    "ExternalLambdaAccessor",
    "./java_bytecode/java_bytecode_parse_lambdas/lambda_examples/"
    "openjdk_8_classes",
    "ExternalLambdaAccessor.test");

  THEN("Then the lambdas should be loaded")
  {
    std::string lambda_name_prefix = "java::ExternalLambdas.lambda$new$";
    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "0:()V");

    require_symbol::require_symbol_exists(
      symbol_table,
      lambda_name_prefix + "1:(ILjava/lang/Object;LDummyGeneric;)V");

    require_symbol::require_symbol_exists(
      symbol_table,
      lambda_name_prefix + "2:([I[Ljava/lang/Object;[LDummyGeneric;)V");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "3:()I");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "4:()Ljava/lang/Object;");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "5:()LDummyGeneric;");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "6:()[I");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "7:()[Ljava/lang/Object;");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "8:()[LDummyGeneric;");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "9:()I");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "10:()Ljava/lang/Object;");

    require_symbol::require_symbol_exists(
      symbol_table, lambda_name_prefix + "11:()LDummyGeneric;");
  }
}
