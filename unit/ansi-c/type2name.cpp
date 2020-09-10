/*******************************************************************\

Module: Unit tests for type_name2type_identifier

Author: Thomas Spriggs

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <numeric>

extern std::string type_name2type_identifier(const std::string &name);

TEST_CASE(
  "type_name2type_identifier sanity check",
  "[core][ansi-c][type_name2type_identifier]")
{
  CHECK(type_name2type_identifier("char") == "char");
}

TEST_CASE(
  "type_name2type_identifier special characters",
  "[core][ansi-c][type_name2type_identifier]")
{
  CHECK(type_name2type_identifier("char*") == "char_ptr_");
  CHECK(type_name2type_identifier("foo{bar}") == "foo_start_sub_bar_end_sub_");
}

/**
 * @return A string containing all 7-bit ascii printable characters.
 */
static std::string all_printable_characters()
{
  const char first = 32;
  const char last = 127;
  std::string printable_characters(last - first, ' ');
  std::iota(printable_characters.begin(), printable_characters.end(), first);
  return printable_characters;
}

TEST_CASE(
  "type_name2type_identifier invalid characters",
  "[core][ansi-c][type_name2type_identifier]")
{
  const std::string printable_characters = all_printable_characters();
  CHECK(
    printable_characters ==
    R"( !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`)"
    R"(abcdefghijklmnopqrstuvwxyz{|}~)");
  CHECK(
    type_name2type_identifier(printable_characters) ==
    "_ptr_0123456789_ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz_"
    "start_sub_end_sub_");
}

TEST_CASE(
  "type_name2type_identifier leading characters",
  "[core][ansi-c][type_name2type_identifier]")
{
  CHECK(
    type_name2type_identifier("0123456789banana_0123456789_split_0123456789") ==
    "banana_0123456789_split_0123456789");
  CHECK(type_name2type_identifier("0123456789_banana") == "_banana");
  CHECK(type_name2type_identifier("_0123456789") == "_0123456789");
}

TEST_CASE(
  "type_name2type_identifier UTF-8 characters",
  "[core][ansi-c][type_name2type_identifier]")
{
  const std::string utf8_example = "\xF0\x9F\x8D\x8C\xF0\x9F\x8D\xA8";
  CHECK(type_name2type_identifier(utf8_example) == utf8_example);
}
