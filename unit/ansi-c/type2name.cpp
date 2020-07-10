/*******************************************************************\

Module: Unit tests for type_name2type_identifier

Author: Thomas Spriggs

\*******************************************************************/

#include <testing-utils/use_catch.h>

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
