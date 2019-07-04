/******************************************************************\

Module: goto_harness_generator

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_generator.h"

#include <list>
#include <string>

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/string2int.h>

// NOLINTNEXTLINE(readability/namespace)
namespace harness_options_parser
{
std::string require_exactly_one_value(
  const std::string &option,
  const std::list<std::string> &values)
{
  if(values.size() != 1)
  {
    throw invalid_command_line_argument_exceptiont{"expected exactly one value",
                                                   "--" + option};
  }

  return values.front();
}

void assert_no_values(
  const std::string &option,
  const std::list<std::string> &values)
{
  PRECONDITION_WITH_DIAGNOSTICS(values.empty(), option);
}

std::size_t require_one_size_value(
  const std::string &option,
  const std::list<std::string> &values)
{
  auto const string_value = require_exactly_one_value(option, values);
  auto value = string2optional<std::size_t>(string_value, 10);
  if(value.has_value())
  {
    return value.value();
  }
  else
  {
    throw invalid_command_line_argument_exceptiont{
      "failed to parse '" + string_value + "' as integer", "--" + option};
  }
}
// NOLINTNEXTLINE(readability/namespace)
} // namespace harness_options_parser
