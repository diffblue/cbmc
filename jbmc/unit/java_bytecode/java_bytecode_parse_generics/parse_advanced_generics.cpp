// Copyright 2019 Diffblue Limited.

/// \file
/// Unit tests for parsing generics using the exact method

#include <java_bytecode/java_type_signature_parser.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "parse_java_type_signature",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  WHEN("A complex generic class signature is parsed")
  {
    java_class_type_signaturet result(
      "<TT:LU<Ljava/lang/Integer;Ljava/lang/String;>;:"
      "LMyInterface<Ljava/lang/String;>;>"
      "LU<TTT;Ljava/lang/String;>;LMyInterface<Ljava/lang/String;>;",
      {});
    THEN("The pretty-printed version is as expected")
    {
      std::stringstream output;
      output << result;
      REQUIRE(
        output.str() ==
        "class Foo<TT extends U<java.lang.Integer, java.lang.String> "
        "& MyInterface<java.lang.String>> "
        "extends U<TT, java.lang.String> "
        "implements MyInterface<java.lang.String>");
    }
  }
  WHEN("A generic method signature is parsed")
  {
    java_method_type_signaturet result("<T:LA;>()TT;", {});
    THEN("The pretty-printed version is as expected")
    {
      std::stringstream output;
      output << result;
      REQUIRE(output.str() == "T f<T extends A>()");
    }
  }
  WHEN("A generic array signature is parsed")
  {
    std::shared_ptr<java_value_type_signaturet> result =
      java_value_type_signaturet::parse_single_value_type(
        "[LMyInterface<Ljava/lang/Object;>;", {});
    THEN("The pretty-printed version is as expected")
    {
      std::stringstream output;
      output << *result;
      REQUIRE(output.str() == "MyInterface<java.lang.Object>[]");
    }
  }
  WHEN(
    "The signature of a generic class with a recursive type reference via an "
    "interface bound on a type parameter is parsed")
  {
    java_class_type_signaturet result(
      "<T::LMyInterface<TT;>;>Ljava/lang/Object;", {});
    THEN("The pretty-printed version is as expected")
    {
      std::stringstream output;
      output << result;
      REQUIRE(
        output.str() ==
        "class Foo<T extends MyInterface<T>> extends java.lang.Object");
    }
  }
}
