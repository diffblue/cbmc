/*******************************************************************\

Module: Unit tests for string2int.h

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/string2int.h>

#include <testing-utils/use_catch.h>

#include <cstdint>

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

// Tests for string2optional<T> template directly

TEST_CASE(
  "string2optional with various integral types",
  "[core][util][string2int]")
{
  REQUIRE(
    string2optional<long long>("9223372036854775807") == 9223372036854775807LL);
  REQUIRE(
    string2optional<long long>("-9223372036854775808") ==
    (-9223372036854775807LL - 1));
  REQUIRE(
    string2optional<unsigned long long>("18446744073709551615") ==
    18446744073709551615ULL);
  REQUIRE(string2optional<std::int16_t>("32767") == 32767);
  REQUIRE(string2optional<std::int16_t>("-32768") == -32768);
}

TEST_CASE(
  "string2optional overflow returns nullopt",
  "[core][util][string2int]")
{
  // signed overflow (use types with guaranteed width)
  REQUIRE(!string2optional<std::int32_t>("2147483648").has_value());
  REQUIRE(!string2optional<std::int32_t>("-2147483649").has_value());
  REQUIRE(!string2optional<std::int16_t>("32768").has_value());
  // unsigned overflow
  REQUIRE(!string2optional<std::uint32_t>("4294967296").has_value());
  REQUIRE(
    !string2optional<unsigned long long>("18446744073709551616").has_value());
}

TEST_CASE(
  "string2optional rejects negative input for unsigned types",
  "[core][util][string2int]")
{
  REQUIRE(!string2optional<unsigned>("-1").has_value());
  REQUIRE(!string2optional<unsigned long long>("-42").has_value());
  REQUIRE(!string2optional<std::size_t>("-100").has_value());
}

TEST_CASE("string2optional rejects partial parses", "[core][util][string2int]")
{
  // trailing non-digit characters must cause rejection
  REQUIRE(!string2optional<int>("123abc").has_value());
  REQUIRE(!string2optional<int>("42 ").has_value());
  REQUIRE(!string2optional<unsigned>("99x").has_value());
}

TEST_CASE(
  "string2optional rejects leading whitespace",
  "[core][util][string2int]")
{
  // from_chars does not skip whitespace (unlike stoll/stoull)
  REQUIRE(!string2optional<int>(" 42").has_value());
  REQUIRE(!string2optional<int>("\t7").has_value());
  REQUIRE(!string2optional<unsigned>(" 1").has_value());
}

TEST_CASE("string2optional rejects empty string", "[core][util][string2int]")
{
  REQUIRE(!string2optional<int>("").has_value());
  REQUIRE(!string2optional<unsigned>("").has_value());
  REQUIRE(!string2optional<long long>("").has_value());
}

TEST_CASE("string2optional with different bases", "[core][util][string2int]")
{
  REQUIRE(string2optional<int>("FF", 16) == 255);
  REQUIRE(string2optional<int>("ff", 16) == 255);
  REQUIRE(string2optional<int>("77", 8) == 63);
  REQUIRE(string2optional<int>("101", 2) == 5);
  REQUIRE(string2optional<unsigned long long>("DEADBEEF", 16) == 0xDEADBEEFULL);
}

TEST_CASE(
  "string2optional accepts a non-null-terminated string_view",
  "[core][util][string2int]")
{
  // The string_view is not null-terminated — this is the case where
  // string_view is meaningfully different from std::string.
  REQUIRE(string2optional<int>(std::string_view{"123abc", 3}) == 123);
  REQUIRE(string2optional<int>(std::string_view{"abc", 1}, 16) == 0xa);
  REQUIRE(string2optional<unsigned>(std::string_view{"42xyz", 2}) == 42u);
  REQUIRE(!string2optional<int>(std::string_view{"123abc", 4}).has_value());
}

TEST_CASE(
  "safe_string2unsigned and safe_string2size_t",
  "[core][util][string2int]")
{
  REQUIRE(safe_string2unsigned("0") == 0u);
  REQUIRE(safe_string2unsigned("123") == 123u);
  REQUIRE(safe_string2unsigned("FF", 16) == 255u);
  REQUIRE(safe_string2size_t("0") == 0u);
  REQUIRE(safe_string2size_t("999") == 999u);
  REQUIRE(safe_string2size_t("10", 16) == 16u);

  // Verify these also work with a non-null-terminated string_view
  REQUIRE(safe_string2unsigned(std::string_view{"42xyz", 2}) == 42u);
  REQUIRE(safe_string2size_t(std::string_view{"99end", 2}) == 99u);
}
