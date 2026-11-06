/*******************************************************************\

Module: Unit tests for cpp_parser

Author: Daniel Kroening

\*******************************************************************/

#include <util/config.h>

#include <cpp/cpp_parser.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE("Parse empty C++ file", "[core][cpp][cpp_parser]")
{
  config = configt{};
  config.ansi_c.set_ILP32();

  std::istringstream in("");

  cpp_parsert parser(null_message_handler);
  parser.in = &in;

  REQUIRE(parser.parse() == false);
}

TEST_CASE("Parse simple C++ code", "[core][cpp][cpp_parser]")
{
  config = configt{};
  config.ansi_c.set_ILP32();

  std::istringstream in("int main() { return 0; }\n");

  cpp_parsert parser(null_message_handler);
  parser.in = &in;

  REQUIRE(parser.parse() == false);
}

TEST_CASE("Parse C++ with class", "[core][cpp][cpp_parser]")
{
  config = configt{};
  config.ansi_c.set_ILP32();

  std::istringstream in("class MyClass { public: int x; };\n");

  cpp_parsert parser(null_message_handler);
  parser.in = &in;

  REQUIRE(parser.parse() == false);
}
