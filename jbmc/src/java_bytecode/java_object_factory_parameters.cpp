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
    auto interval = interval_uniont::of_string(interval_string);
    if(!interval.has_value())
    {
      throw invalid_command_line_argument_exceptiont(
        "argument must be a comma-seperated sequence of intervals of the form"
        " [int:int], [int:] or [:int]",
        "--java-assume-inputs-interval");
    }
    if(interval->is_empty())
    {
      throw invalid_command_line_argument_exceptiont(
        "interval is empty, lower limit cannot be bigger than upper limit",
        "--java-assume-inputs-interval");
    }
    assume_inputs_interval = *interval;
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
