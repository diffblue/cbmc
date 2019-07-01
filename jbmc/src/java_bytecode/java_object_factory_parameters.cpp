/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "java_object_factory_parameters.h"

#include <regex>

#include <util/cmdline.h>
#include <util/options.h>
#include <util/validate.h>

void java_object_factory_parameterst::set(const optionst &options)
{
  object_factory_parameterst::set(options);

  if(options.is_set("java-assume-inputs-interval"))
  {
    const auto &interval_string =
      options.get_option("java-assume-inputs-interval");
    const std::regex limits_regex("\\[(-\\d+|\\d*):(-\\d+|\\d*)\\]");
    std::smatch base_match;
    if(!std::regex_match(interval_string, base_match, limits_regex))
    {
      throw invalid_command_line_argument_exceptiont(
        "interval must be of the form [int:int], [int:] or [:int]",
        "--java-assume-inputs-interval");
    }
    assume_inputs_interval = [&]() -> integer_intervalt {
      integer_intervalt interval;
      if(!base_match[1].str().empty())
        interval.make_ge_than(string2integer(base_match[1].str()));
      if(!base_match[2].str().empty())
        interval.make_le_than(string2integer(base_match[2].str()));
      if(interval.is_top())
        throw invalid_command_line_argument_exceptiont(
          "at least one of the interval bounds must be given",
          "--java-assume-inputs-interval");
      if(interval.empty())
        throw invalid_command_line_argument_exceptiont(
          "interval is empty, lower limit cannot be bigger than upper limit",
          "--java-assume-inputs-interval");
      return interval;
    }();
  }
  assume_inputs_integral = options.is_set("java-assume-inputs-integral");
}

void parse_java_object_factory_options(
  const cmdlinet &cmdline,
  optionst &options)
{
  parse_object_factory_options(cmdline, options);

  if(cmdline.isset("java-assume-inputs-interval"))
  {
    options.set_option(
      "java-assume-inputs-interval",
      cmdline.get_value("java-assume-inputs-interval"));
  }
  if(cmdline.isset("java-assume-inputs-integral"))
  {
    options.set_option("java-assume-inputs-integral", true);
  }
}
