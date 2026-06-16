/*******************************************************************\

Module: Unit tests for file_converter

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for the file_converter byte-array generator

#include <ansi-c/file_converter.h>
#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE(
  "file_converter emits byte-value initialisers",
  "[core][ansi-c][file_converter]")
{
  SECTION("a byte with the high bit set is cast to char")
  {
    // {0x80, 'A'}; the cast keeps the initialiser valid for signed char.
    std::istringstream in(std::string{
      "\x80"
      "A",
      2});
    std::ostringstream out;
    file_converter_append(in, out, false, "x");
    REQUIRE(out.str() == "(char)128,65,'\\n',\n");
  }

  SECTION("a trailing carriage return is stripped (CRLF input)")
  {
    std::istringstream in("ab\r\ncd\r\n");
    std::ostringstream out;
    file_converter_append(in, out, false, "x");
    REQUIRE(out.str() == "97,98,'\\n',\n99,100,'\\n',\n");
  }

  SECTION("--line emits a #line directive naming the file")
  {
    std::istringstream in("z");
    std::ostringstream out;
    file_converter_append(in, out, true, "hdr.h");
    // bytes of `#line 1 "hdr.h"\n`, a physical break, then `z` + newline byte
    REQUIRE(
      out.str() ==
      "35,108,105,110,101,32,49,32,34,104,100,114,46,104,34,10,\n"
      "122,'\\n',\n");
  }
}
