/******************************************************************\

Module: goto_harness_generator_factory

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_generator_factory.h"

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/string_utils.h>

#include <algorithm>
#include <functional>
#include <iterator>
#include <sstream>
#include <string>

void goto_harness_generator_factoryt::register_generator(
  std::string generator_name,
  build_generatort build_generator)
{
  PRECONDITION(generators.find(generator_name) == generators.end());
  auto res = generators.insert({generator_name, build_generator});
  CHECK_RETURN(res.second);
}

std::unique_ptr<goto_harness_generatort>
goto_harness_generator_factoryt::factory(
  const std::string &generator_name,
  const generator_optionst &generator_options,
  const goto_modelt &goto_model)
{
  auto it = generators.find(generator_name);

  if(it != generators.end())
  {
    auto generator = it->second();
    for(const auto &option : generator_options)
    {
      generator->handle_option(option.first, option.second);
    }
    generator->validate_options(goto_model);

    return generator;
  }
  else
  {
    throw invalid_command_line_argument_exceptiont(
      "unknown generator type",
      "--" GOTO_HARNESS_GENERATOR_TYPE_OPT,
      join_strings(
        std::ostringstream(),
        generators.begin(),
        generators.end(),
        ", ",
        [](const std::pair<std::string, build_generatort> &value) {
          return value.first;
        })
        .str());
  }
}
