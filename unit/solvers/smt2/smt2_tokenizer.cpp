// Author: Daniel Kroening

/// \file
/// Unit tests for smt2_tokenizert

#include <solvers/smt2/smt2_tokenizer.h>
#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE("smt2 tokenizer end of file", "[core][solvers][smt2]")
{
  std::istringstream in{""};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::END_OF_FILE);
}

TEST_CASE("smt2 tokenizer open/close parentheses", "[core][solvers][smt2]")
{
  std::istringstream in{"()"};
  smt2_tokenizert tokenizer{in};
  auto tok1 = tokenizer.next_token();
  REQUIRE(tok1.kind == smt2_tokenizert::OPEN);
  auto tok2 = tokenizer.next_token();
  REQUIRE(tok2.kind == smt2_tokenizert::CLOSE);
  auto tok3 = tokenizer.next_token();
  REQUIRE(tok3.kind == smt2_tokenizert::END_OF_FILE);
}

TEST_CASE("smt2 tokenizer simple symbol", "[core][solvers][smt2]")
{
  std::istringstream in{"abc"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(tok.text == "abc");
  REQUIRE_FALSE(tok.quoted_symbol);
}

TEST_CASE("smt2 tokenizer quoted symbol", "[core][solvers][smt2]")
{
  std::istringstream in{"|hello world|"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(tok.text == "hello world");
  REQUIRE(tok.quoted_symbol);
}

TEST_CASE("smt2 tokenizer string literal", "[core][solvers][smt2]")
{
  std::istringstream in{"\"hello\""};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::STRING_LITERAL);
  REQUIRE(tok.text == "hello");
}

TEST_CASE("smt2 tokenizer escaped quotes in string", "[core][solvers][smt2]")
{
  std::istringstream in{"\"say \"\"hi\"\"\""};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::STRING_LITERAL);
  REQUIRE(tok.text == "say \"hi\"");
}

TEST_CASE("smt2 tokenizer decimal numeral", "[core][solvers][smt2]")
{
  std::istringstream in{"42"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::NUMERAL);
  REQUIRE(tok.text == "42");
}

TEST_CASE("smt2 tokenizer binary numeral", "[core][solvers][smt2]")
{
  std::istringstream in{"#b1010"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::NUMERAL);
  REQUIRE(tok.text == "#b1010");
}

TEST_CASE("smt2 tokenizer hex numeral", "[core][solvers][smt2]")
{
  std::istringstream in{"#xFF"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::NUMERAL);
  REQUIRE(tok.text == "#xFF");
}

TEST_CASE("smt2 tokenizer keyword", "[core][solvers][smt2]")
{
  std::istringstream in{":status"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::KEYWORD);
  REQUIRE(tok.text == "status");
}

TEST_CASE("smt2 tokenizer skips whitespace", "[core][solvers][smt2]")
{
  std::istringstream in{"  \t\r\n abc"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(tok.text == "abc");
}

TEST_CASE("smt2 tokenizer skips comments", "[core][solvers][smt2]")
{
  std::istringstream in{"; this is a comment\nabc"};
  smt2_tokenizert tokenizer{in};
  auto tok = tokenizer.next_token();
  REQUIRE(tok.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(tok.text == "abc");
}

TEST_CASE("smt2 tokenizer peek", "[core][solvers][smt2]")
{
  std::istringstream in{"abc def"};
  smt2_tokenizert tokenizer{in};
  const auto &peeked = tokenizer.peek();
  REQUIRE(peeked.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(peeked.text == "abc");
  // peek again returns same token
  const auto &peeked2 = tokenizer.peek();
  REQUIRE(peeked2.text == "abc");
  // next_token consumes the peeked token
  auto tok = tokenizer.next_token();
  REQUIRE(tok.text == "abc");
  auto tok2 = tokenizer.next_token();
  REQUIRE(tok2.text == "def");
}

TEST_CASE("smt2 tokenizer line number tracking", "[core][solvers][smt2]")
{
  std::istringstream in{"abc\ndef"};
  smt2_tokenizert tokenizer{in};
  auto tok1 = tokenizer.next_token();
  REQUIRE(tok1.line_no == 1);
  auto tok2 = tokenizer.next_token();
  REQUIRE(tok2.line_no == 2);
}

TEST_CASE(
  "smt2 tokenizer error on EOF in quoted symbol",
  "[core][solvers][smt2]")
{
  std::istringstream in{"|unterminated"};
  smt2_tokenizert tokenizer{in};
  REQUIRE_THROWS_AS(tokenizer.next_token(), smt2_tokenizert::smt2_errort);
}

TEST_CASE(
  "smt2 tokenizer error on EOF in string literal",
  "[core][solvers][smt2]")
{
  std::istringstream in{"\"unterminated"};
  smt2_tokenizert tokenizer{in};
  REQUIRE_THROWS_AS(tokenizer.next_token(), smt2_tokenizert::smt2_errort);
}

TEST_CASE("smt2 tokenizer error on unknown numeral", "[core][solvers][smt2]")
{
  std::istringstream in{"#z"};
  smt2_tokenizert tokenizer{in};
  REQUIRE_THROWS_AS(tokenizer.next_token(), smt2_tokenizert::smt2_errort);
}

TEST_CASE("smt2 tokenizer error on illegal character", "[core][solvers][smt2]")
{
  std::istringstream in{"\\"};
  smt2_tokenizert tokenizer{in};
  REQUIRE_THROWS_AS(tokenizer.next_token(), smt2_tokenizert::smt2_errort);
}

TEST_CASE("is_smt2_simple_symbol_character", "[core][solvers][smt2]")
{
  REQUIRE(is_smt2_simple_symbol_character('a'));
  REQUIRE(is_smt2_simple_symbol_character('Z'));
  REQUIRE(is_smt2_simple_symbol_character('0'));
  REQUIRE(is_smt2_simple_symbol_character('_'));
  REQUIRE(is_smt2_simple_symbol_character('+'));
  REQUIRE(is_smt2_simple_symbol_character('~'));
  REQUIRE_FALSE(is_smt2_simple_symbol_character(' '));
  REQUIRE_FALSE(is_smt2_simple_symbol_character('('));
  REQUIRE_FALSE(is_smt2_simple_symbol_character(')'));
  REQUIRE_FALSE(is_smt2_simple_symbol_character('"'));
}

TEST_CASE(
  "smt2 tokenizer: quoted_symbol resets between tokens",
  "[core][solvers][smt2]")
{
  // Regression test: the latent bug was that helpers other than
  // get_simple_symbol/get_quoted_symbol never wrote token.quoted_symbol,
  // so a NUMERAL or STRING_LITERAL emitted right after a |...| symbol
  // would inherit quoted_symbol == true.  After the refactor each
  // helper produces a fresh tokent with quoted_symbol default-
  // initialised to false; lock that in.
  std::istringstream in{"|foo| bar 42 #b10 #xff \"x\" :kw"};
  smt2_tokenizert tokenizer{in};
  auto t = tokenizer.next_token();
  REQUIRE(t.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(t.quoted_symbol);
  for(int i = 0; i < 6; ++i)
  {
    auto next = tokenizer.next_token();
    REQUIRE_FALSE(next.quoted_symbol);
  }
}

TEST_CASE(
  "smt2 tokenizer: implicit conversion to token_kindt",
  "[core][solvers][smt2]")
{
  // The parser uses both `switch(token)` and `token == OPEN`. Lock the
  // implicit conversion into the test suite so future changes to
  // tokent don't break the parser silently.
  std::istringstream in{"(abc)"};
  smt2_tokenizert tokenizer{in};
  auto t = tokenizer.next_token();
  // operator==
  REQUIRE(t == smt2_tokenizert::OPEN);
  REQUIRE_FALSE(t == smt2_tokenizert::CLOSE);
  // switch dispatch
  bool dispatched_to_open = false;
  switch(t)
  {
  case smt2_tokenizert::OPEN:
    dispatched_to_open = true;
    break;
  case smt2_tokenizert::NONE:
  case smt2_tokenizert::END_OF_FILE:
  case smt2_tokenizert::STRING_LITERAL:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::SYMBOL:
  case smt2_tokenizert::KEYWORD:
  case smt2_tokenizert::CLOSE:
    break;
  }
  REQUIRE(dispatched_to_open);
}

TEST_CASE(
  "smt2 tokenizer: error() reports current line",
  "[core][solvers][smt2]")
{
  std::istringstream in{"abc\n\ndef\nghi"};
  smt2_tokenizert tokenizer{in};
  (void)tokenizer.next_token(); // abc, line 1
  (void)tokenizer.next_token(); // def, line 3
  REQUIRE(tokenizer.error("x").get_line_no() == 3);
  (void)tokenizer.next_token(); // ghi, line 4
  REQUIRE(tokenizer.error("x").get_line_no() == 4);
  // and the no-message variant
  REQUIRE(tokenizer.error().get_line_no() == 4);
}

TEST_CASE(
  "smt2 tokenizer: line_no preserved across peek and consume",
  "[core][solvers][smt2]")
{
  std::istringstream in{"abc\n\ndef"};
  smt2_tokenizert tokenizer{in};
  (void)tokenizer.next_token();
  REQUIRE(tokenizer.peek().line_no == 3);
  REQUIRE(tokenizer.next_token().line_no == 3);
}

TEST_CASE(
  "smt2 tokenizer: line_no advances inside multi-line quoted symbol",
  "[core][solvers][smt2]")
{
  std::istringstream in{"|a\nb\nc|"};
  smt2_tokenizert tokenizer{in};
  auto t = tokenizer.next_token();
  REQUIRE(t.kind == smt2_tokenizert::SYMBOL);
  REQUIRE(t.text == "a\nb\nc");
  REQUIRE(t.quoted_symbol);
  REQUIRE(t.line_no == 3);
}

TEST_CASE("smt2 tokenizer error on EOF after #", "[core][solvers][smt2]")
{
  // Hits the `unexpected EOF in numeral token` branch in read_token.
  std::istringstream in{"#"};
  smt2_tokenizert tokenizer{in};
  REQUIRE_THROWS_AS(tokenizer.next_token(), smt2_tokenizert::smt2_errort);
}

TEST_CASE("smt2 tokenizer error on bare colon", "[core][solvers][smt2]")
{
  // Hits the `expecting symbol after colon` branch in read_token:
  // get_simple_symbol() returns END_OF_FILE because no symbol
  // character follows.
  std::istringstream in{":"};
  smt2_tokenizert tokenizer{in};
  REQUIRE_THROWS_AS(tokenizer.next_token(), smt2_tokenizert::smt2_errort);
}
