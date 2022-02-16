/// Author: Diffblue Ltd.

#include <testing-utils/smt2irep.h>

#include <solvers/smt2/smt2irep.h>
#include <util/message.h>

#include <sstream>

bool operator==(
  const smt2_parser_test_resultt &left,
  const smt2_parser_test_resultt &right)
{
  return left.parsed_output == right.parsed_output &&
         left.messages == right.messages;
}

smt2_parser_test_resultt smt2irep(const std::string &input)
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

smt2_parser_test_resultt smt2_parser_success(irept parse_tree)
{
  return {std::move(parse_tree), ""};
}
