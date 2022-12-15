// Author: Diffblue Ltd.

// Note that this test should not include any headers which are internal to
// cbmc. API headers (and STL/catch) should be included only. This is in order
// to confirm that the API can be used without reference to cmbc internals.

#include <libcprover-cpp/api.h>

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "../catch/catch.hpp"

class contains_in_ordert final
  : public Catch::MatcherBase<std::vector<std::string>>
{
public:
  contains_in_ordert(std::initializer_list<std::string> expected);
  bool match(const std::vector<std::string> &actual) const override;

protected:
  std::string describe() const override;

private:
  std::vector<std::string> expected;
};

contains_in_ordert::contains_in_ordert(
  std::initializer_list<std::string> expected)
  : expected{
      std::make_move_iterator(expected.begin()),
      std::make_move_iterator(expected.end())}
{
}

bool contains_in_ordert::match(const std::vector<std::string> &actual) const
{
  auto begin_search = actual.begin();
  for(const auto &expected_item : expected)
  {
    auto find_result = std::find(begin_search, actual.end(), expected_item);
    if(find_result == actual.end())
      return false;
    else
      begin_search = ++find_result;
  }
  return true;
}

std::string contains_in_ordert::describe() const
{
  std::stringstream description;
  description << "contains these strings in order ";
  description << '"' << *expected.begin() << '"';
  for(auto iterator = std::next(expected.begin()); iterator != expected.end();
      ++iterator)
  {
    description << ", \"" << *iterator << '"';
  }
  return description.str();
}

TEST_CASE("Test loading model from file.", "[core][libcprover-cpp]")
{
  api_sessiont api(api_optionst::create());

  std::vector<std::string> output;
  // This lambda needs to be non-capturing in order for it to be convertible
  // to a function pointer, to pass to the API.
  const auto write_output =
    [](const api_messaget &message, api_call_back_contextt context) {
      std::vector<std::string> &output =
        *static_cast<std::vector<std::string> *>(context);
      output.emplace_back(api_message_get_string(message));
    };

  api.set_message_callback(write_output, &output);
  api.load_model_from_files({"test.c"});
  CHECK_THAT(
    output,
    (contains_in_ordert{
      "Parsing test.c",
      "Converting",
      "Type-checking test",
      "Generating GOTO Program"}));
}
