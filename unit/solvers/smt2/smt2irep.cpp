// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2/smt2irep.h>
#include <util/message.h>

#include <sstream>
#include <string>
#include <utility>

struct smt2_parser_test_resultt
{
  optionalt<irept> parsed_output;
  std::string messages;
};

bool operator==(
  const smt2_parser_test_resultt &left,
  const smt2_parser_test_resultt &right)
{
  return left.parsed_output == right.parsed_output &&
         left.messages == right.messages;
}

static smt2_parser_test_resultt smt2irep(const std::string &input)
{
  std::stringstream in_stream(input);
  std::stringstream out_stream;
  stream_message_handlert message_handler(out_stream);
  return {smt2irep(in_stream, message_handler), out_stream.str()};
}

std::ostream &operator<<(
  std::ostream &output_stream,
  const smt2_parser_test_resultt &test_result)
{
  const std::string printed_irep =
    test_result.parsed_output.has_value()
      ? '{' + test_result.parsed_output->pretty(0, 0) + '}'
      : "empty optional irep";
  output_stream << '{' << printed_irep << ", \"" << test_result.messages
                << "\"}";
  return output_stream;
}

class smt2_parser_error_containingt
  : public Catch::MatcherBase<smt2_parser_test_resultt>
{
public:
  explicit smt2_parser_error_containingt(std::string expected_error);
  bool match(const smt2_parser_test_resultt &exception) const override;
  std::string describe() const override;

private:
  std::string expected_error;
};

smt2_parser_error_containingt::smt2_parser_error_containingt(
  std::string expected_error)
  : expected_error{std::move(expected_error)}
{
}

bool smt2_parser_error_containingt::match(
  const smt2_parser_test_resultt &result) const
{
  return !result.parsed_output.has_value() &&
         result.messages.find(expected_error) != std::string::npos;
}

std::string smt2_parser_error_containingt::describe() const
{
  return "Expecting empty parse tree and \"" + expected_error +
         "\" printed to output.";
}

static smt2_parser_test_resultt smt2_parser_success(irept parse_tree)
{
  return {std::move(parse_tree), ""};
}

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
