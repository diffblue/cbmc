/*******************************************************************\

Module: Unit tests for string2int.h

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/string2int.h>

TEST_CASE(
  "converting optionally to a valid integer should succeed",
  "[core][util][string2int]")
{
  REQUIRE(string2optional_int("13") == 13);
  REQUIRE(string2optional_int("-5") == -5);
  REQUIRE(string2optional_int("c0fefe", 16) == 0xc0fefe);
}

TEST_CASE(
  "optionally converting invalid string to integer should return nullopt",
  "[core][util][string2int]")
{
  REQUIRE(!string2optional_int("thirteen").has_value());
  REQUIRE(!string2optional_int("c0fefe").has_value());
}

TEST_CASE(
  "optionally converting string out of range to integer should return nullopt",
  "[core][util][string2int]")
{
  REQUIRE(
    !string2optional_int("0xfffffffffffffffffffffffffffffffffffffffffff", 16)
       .has_value());
}

TEST_CASE(
  "converting optionally to a valid unsigned should succeed",
  "[core][util][string2int]")
{
  REQUIRE(string2optional_unsigned("13") == 13u);
  REQUIRE(string2optional_unsigned("c0fefe", 16) == 0xc0fefeu);
}

TEST_CASE(
  "optionally converting invalid string to unsigned should return nullopt",
  "[core][util][string2int]")
{
  REQUIRE(!string2optional_unsigned("thirteen").has_value());
  REQUIRE(!string2optional_unsigned("c0fefe").has_value());
}

TEST_CASE(
  "optionally converting string out of range to unsigned should return nullopt",
  "[core][util][string2int]")
{
  REQUIRE(!string2optional_unsigned(
             "0xfffffffffffffffffffffffffffffffffffffffffff", 16)
             .has_value());
  REQUIRE(!string2optional_unsigned("-5").has_value());
}

TEST_CASE(
  "converting optionally to a valid size_t should succeed",
  "[core][util][string2int]")
{
  REQUIRE(string2optional_size_t("13") == std::size_t{13});
  REQUIRE(string2optional_size_t("c0fefe", 16) == std::size_t{0xc0fefe});
}

TEST_CASE(
  "optionally converting invalid string to size_t should return nullopt",
  "[core][util][string2int]")
{
  REQUIRE(!string2optional_size_t("thirteen").has_value());
  REQUIRE(!string2optional_size_t("c0fefe").has_value());
}

TEST_CASE(
  "optionally converting string out of range to size_t should return nullopt",
  "[core][util][string2int]")
{
  REQUIRE(
    !string2optional_size_t("0xfffffffffffffffffffffffffffffffffffffffffff", 16)
       .has_value());
  REQUIRE(!string2optional_size_t("-5").has_value());
}
