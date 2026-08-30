/*******************************************************************\

Module: Unit tests for CPP lexer/scanner

Author: Daniel Kroening, 2015

\*******************************************************************/

#include <util/config.h>

#include <cpp/cpp_parser.h>
#include <cpp/cpp_token_buffer.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <sstream>
#include <vector>

TEST_CASE("Scan simple C++ tokens", "[core][cpp][cpp_scanner]")
{
  config = configt{};
  config.ansi_c.set_ILP32();

  std::istringstream in("int x = 42;\n");

  cpp_parsert parser(null_message_handler);
  parser.token_buffer.ansi_c_parser.in = &in;
  ansi_c_scanner_init(parser.token_buffer.ansi_c_parser);

  cpp_tokent tk;
  std::vector<std::string> tokens;

  while(parser.token_buffer.get_token(tk))
    tokens.push_back(tk.text);

  REQUIRE(tokens.size() > 0);
  REQUIRE(tokens[0] == "int");
}

TEST_CASE("Scan C++ keywords", "[core][cpp][cpp_scanner]")
{
  config = configt{};
  config.ansi_c.set_ILP32();

  std::istringstream in("class namespace public private\n");

  cpp_parsert parser(null_message_handler);
  parser.token_buffer.ansi_c_parser.in = &in;
  ansi_c_scanner_init(parser.token_buffer.ansi_c_parser);

  cpp_tokent tk;
  std::vector<std::string> tokens;

  while(parser.token_buffer.get_token(tk))
    tokens.push_back(tk.text);

  REQUIRE(tokens.size() == 4);
  REQUIRE(tokens[0] == "class");
  REQUIRE(tokens[1] == "namespace");
}
