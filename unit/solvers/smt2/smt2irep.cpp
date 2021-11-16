// Author: Diffblue Ltd.

#include <testing-utils/smt2irep.h>
#include <testing-utils/use_catch.h>

TEST_CASE("smt2irep error handling", "[core][solvers][smt2]")
{
  CHECK_THAT(
    smt2irep("|"), smt2_parser_error_containingt{"EOF within quoted symbol"});
  CHECK_THAT(
    smt2irep(":"),
    smt2_parser_error_containingt{"expecting symbol after colon"});
  CHECK_THAT(
    smt2irep(":foo"), smt2_parser_error_containingt{"unexpected token"});
  CHECK(smt2irep("") == smt2_parser_test_resultt{{}, ""});
  CHECK_THAT(
    smt2irep("("), smt2_parser_error_containingt{"unexpected end of file"});
  CHECK_THAT(smt2irep(")"), smt2_parser_error_containingt{"unexpected ')'"});
  CHECK_THAT(
    smt2irep("#"),
    smt2_parser_error_containingt{"unexpected EOF in numeral token"});
  CHECK_THAT(
    smt2irep("#0"), smt2_parser_error_containingt{"unknown numeral token"});
  CHECK_THAT(
    smt2irep("\\"), smt2_parser_error_containingt{"unexpected character '\\'"});
}

TEST_CASE("smt2irept parse single tokens", "[core][solvers][smt2]")
{
  CHECK(
    smt2irep("|example_symbol|") ==
    smt2_parser_success({"example_symbol", {}, {}}));
  CHECK(
    smt2irep("\"example string literal\"") ==
    smt2_parser_success({"example string literal", {}, {}}));
  CHECK(smt2irep("#b00101010") == smt2_parser_success({"#b00101010", {}, {}}));
  CHECK(smt2irep("#x2A") == smt2_parser_success({"#x2A", {}, {}}));
}

TEST_CASE("smt2irept comments", "[core][solvers][smt2]")
{
  CHECK(smt2irep(";") == smt2_parser_test_resultt{{}, ""});
  CHECK(smt2irep(";foobar") == smt2_parser_test_resultt{{}, ""});
  CHECK(
    smt2irep("|example_symbol|;foobar") ==
    smt2_parser_success({"example_symbol", {}, {}}));
  CHECK(
    smt2irep(";foobar\n|example_symbol|") ==
    smt2_parser_success({"example_symbol", {}, {}}));
}

TEST_CASE("smt2irept parse with sub trees", "[core][solvers][smt2]")
{
  CHECK(smt2irep("()") == smt2_parser_success({}));
  const irept foo_symbol{"foo", {}, {}};
  CHECK(
    smt2irep("(|foo|)") == smt2_parser_success(irept{"", {}, {foo_symbol}}));
  const irept bar_symbol{"bar", {}, {}};
  CHECK(
    smt2irep("(|foo| |bar|)") ==
    smt2_parser_success(irept{"", {}, {foo_symbol, bar_symbol}}));
  const irept baz_symbol{"baz", {}, {}};
  CHECK(
    smt2irep("(|foo| |bar| |baz|)") ==
    smt2_parser_success(irept{"", {}, {foo_symbol, bar_symbol, baz_symbol}}));
  CHECK(smt2irep("(())") == smt2_parser_success({"", {}, {{}}}));
  CHECK(smt2irep("(() ())") == smt2_parser_success({"", {}, {{}, {}}}));
  CHECK(smt2irep("(() () ())") == smt2_parser_success({"", {}, {{}, {}, {}}}));
  CHECK(
    smt2irep("(|foo| () |bar|)") ==
    smt2_parser_success({"", {}, {foo_symbol, {}, bar_symbol}}));
  CHECK(
    smt2irep("(|foo| (|bar|) |baz|)") ==
    smt2_parser_success(
      {"", {}, {foo_symbol, {"", {}, {bar_symbol}}, baz_symbol}}));
  CHECK(
    smt2irep("((|foo| |bar| |baz|) (|baz| |bar| |foo|))") ==
    smt2_parser_success(
      {"",
       {},
       {irept{"", {}, {foo_symbol, bar_symbol, baz_symbol}},
        irept{"", {}, {baz_symbol, bar_symbol, foo_symbol}}}}));
}
