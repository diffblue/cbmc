/*******************************************************************\

Module: JSON Commandline Interface

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// JSON Commandline Interface

#include "json_interface.h"

#include <util/cmdline.h>
#include <util/exception_utils.h>
#include <util/json.h>
#include <util/message.h>

#include "json_parser.h"

#include <iostream>

/// Parse commandline options from \p json into \p cmdline
static void get_json_options(const json_objectt &json, cmdlinet &cmdline)
{
  const jsont &arguments = json["arguments"];
  if(!arguments.is_array())
  {
    throw invalid_command_line_argument_exceptiont(
      "array expected", "'arguments'");
  }

  for(const auto &argument : to_json_array(arguments))
  {
    if(!argument.is_string())
    {
      throw invalid_command_line_argument_exceptiont(
        "string expected", "argument");
    }

    cmdline.args.push_back(argument.value);
  }

  const jsont &options = json["options"];
  if(!options.is_object())
  {
    throw invalid_command_line_argument_exceptiont(
      "array expected", "'options'");
  }

  for(const auto &option_pair : to_json_object(options))
  {
    if(option_pair.second.is_string() || option_pair.second.is_number())
    {
      // e.g. --option x
      cmdline.set(option_pair.first, option_pair.second.value);
    }
    else if(option_pair.second.is_boolean())
    {
      // e.g. --flag
      if(option_pair.second.is_true())
        cmdline.set(option_pair.first);
    }
    else if(option_pair.second.is_array())
    {
      // e.g. --option x --option y
      for(const auto &element : to_json_array(option_pair.second))
      {
        if(element.is_string())
          cmdline.set(option_pair.first, element.value);
        else
        {
          throw invalid_command_line_argument_exceptiont(
            "string expected", option_pair.first);
        }
      }
    }
    else
    {
      throw invalid_command_line_argument_exceptiont(
        "unrecognized commandline option format",
        option_pair.first,
        "Boolean, string, number, or string array expected");
    }
  }
}

void json_interface(cmdlinet &cmdline, message_handlert &message_handler)
{
  if(cmdline.isset("json-interface"))
  {
    jsont json;

    parse_json(std::cin, "", message_handler, json);

    try
    {
      if(!json.is_object())
      {
        throw invalid_command_line_argument_exceptiont(
          "JSON object expected at top-level", "command-line JSON input");
      }

      get_json_options(to_json_object(json), cmdline);

      // Add this so that it gets propagated into optionst;
      // the ui_message_handlert::uit has already been set on the basis
      // of the json-interface flag.
      cmdline.set("json-ui");
    }
    catch(const invalid_command_line_argument_exceptiont &e)
    {
      messaget log(message_handler);
      log.error() << e.what() << messaget::eom;

      // make sure we fail with a usage error
      cmdline.clear();
    }
  }
}
