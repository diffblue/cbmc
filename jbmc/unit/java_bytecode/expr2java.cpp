/*******************************************************************\

Module: Unit tests for expr-to-java string conversion

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java_bytecode/expr2java.h>

TEST_CASE(
  "expr2java tests",
  "[core][java_bytecode][expr2java][floating_point_to_java_string]")
{
  SECTION("0.0 double to string")
  {
    REQUIRE(floating_point_to_java_string(0.0) == "0.0");
  }

  SECTION("0.0 float to string")
  {
    REQUIRE(floating_point_to_java_string(0.0f) == "0.0f");
  }

  SECTION("-0.0 double to string")
  {
    REQUIRE(floating_point_to_java_string(-0.0) == "-0.0");
  }

  SECTION("-0.0 float to string")
  {
    REQUIRE(floating_point_to_java_string(-0.0f) == "-0.0f");
  }

  SECTION("1.0 double to string")
  {
    REQUIRE(floating_point_to_java_string(1.0) == "1.0");
  }

  SECTION("1.0 float to string")
  {
    REQUIRE(floating_point_to_java_string(1.0f) == "1.0f");
  }

  SECTION("-1.0 double to string")
  {
    REQUIRE(floating_point_to_java_string(-1.0) == "-1.0");
  }

  SECTION("-1.0 float to string")
  {
    REQUIRE(floating_point_to_java_string(-1.0f) == "-1.0f");
  }

  SECTION("Infinity double to string")
  {
    REQUIRE(
      floating_point_to_java_string(static_cast<double>(INFINITY)) ==
      "Double.POSITIVE_INFINITY");
  }

  SECTION("Infinity float to string")
  {
    REQUIRE(
      floating_point_to_java_string(static_cast<float>(INFINITY)) ==
      "Float.POSITIVE_INFINITY");
  }

  SECTION("Negative infinity double to string")
  {
    REQUIRE(
      floating_point_to_java_string(static_cast<double>(-INFINITY)) ==
      "Double.NEGATIVE_INFINITY");
  }

  SECTION("Negative infinity float to string")
  {
    REQUIRE(
      floating_point_to_java_string(static_cast<float>(-INFINITY)) ==
      "Float.NEGATIVE_INFINITY");
  }

  SECTION("Float NaN to string")
  {
    REQUIRE(
      floating_point_to_java_string(static_cast<float>(NAN)) == "Float.NaN");
  }

  SECTION("Double NaN to string")
  {
    REQUIRE(
      floating_point_to_java_string(static_cast<double>(NAN)) == "Double.NaN");
  }

  SECTION("Hex float to string (print a comment)")
  {
    const float value = std::strtod("0x1p+37f", nullptr);
#ifndef _MSC_VER
    REQUIRE(
      floating_point_to_java_string(value) == "0x1p+37f /* 1.37439e+11 */");
#else
    REQUIRE(
      floating_point_to_java_string(value) ==
      "0x1.000000p+37f /* 1.37439e+11 */");
#endif
  }

  SECTION("Hex double to string (print a comment)")
  {
    const double value = std::strtod("0x1p+37f", nullptr);
#ifndef _MSC_VER
    REQUIRE(
      floating_point_to_java_string(value) == "0x1p+37 /* 1.37439e+11 */");
#else
    REQUIRE(
      floating_point_to_java_string(value) ==
      "0x1.000000p+37 /* 1.37439e+11 */");
#endif
  }

  SECTION("Beyond numeric limits")
  {
#ifndef _MSC_VER
    REQUIRE(
      floating_point_to_java_string(-5.56268e-309)
        .find("/* -5.56268e-309 */") != std::string::npos);
#else
    REQUIRE(floating_point_to_java_string(-5.56268e-309) == "-5.56268e-309");
#endif
  }
}
