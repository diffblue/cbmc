/******************************************************************\

Module: goto_harness_generator

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_generator.h"

#include <list>
#include <string>

#include <util/exception_utils.h>
#include <util/invariant.h>

std::string goto_harness_generatort::require_exactly_one_value(
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

void goto_harness_generatort::assert_no_values(
  const std::string &option,
  const std::list<std::string> &values)
{
  PRECONDITION_WITH_DIAGNOSTICS(values.empty(), option);
}
