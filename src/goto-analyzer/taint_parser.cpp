/*******************************************************************\

Module: Taint Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Taint Parser

#include "taint_parser.h"

#include <ostream>

#include <util/string2int.h>

#include <json/json_parser.h>

bool taint_parser(
  const std::string &file_name,
  taint_parse_treet &dest,
  message_handlert &message_handler)
{
  jsont json;

  if(parse_json(file_name, message_handler, json))
  {
    messaget message(message_handler);
    message.error() << "taint file is not a valid json file"
                    << messaget::eom;
    return true;
  }

  if(!json.is_array())
  {
    messaget message(message_handler);
    message.error() << "expecting an array in the taint file, but got "
                    << json << messaget::eom;
    return true;
  }

  for(const auto &taint_spec : to_json_array(json))
  {
    if(!taint_spec.is_object())
    {
      messaget message(message_handler);
      message.error() << "expecting an array of objects "
                      << "in the taint file, but got " << taint_spec
                      << messaget::eom;
      return true;
    }

    taint_parse_treet::rulet rule;

    const std::string kind = taint_spec["kind"].value;

    if(kind=="source")
      rule.kind=taint_parse_treet::rulet::SOURCE;
    else if(kind=="sink")
      rule.kind=taint_parse_treet::rulet::SINK;
    else if(kind=="sanitizer")
      rule.kind=taint_parse_treet::rulet::SANITIZER;
    else
    {
      messaget message(message_handler);
      message.error() << "taint rule must have \"kind\" which is "
                         "\"source\" or \"sink\" or \"sanitizer\""
                      << messaget::eom;
      return true;
    }

    const std::string function = taint_spec["function"].value;

    if(function.empty())
    {
      messaget message(message_handler);
      message.error() << "taint rule must have \"function\""
                      << messaget::eom;
      return true;
    }
    else
      rule.function_identifier=function;

    const std::string where = taint_spec["where"].value;

    if(where=="return_value")
    {
      rule.where=taint_parse_treet::rulet::RETURN_VALUE;
    }
    else if(where == id2string(ID_this))
    {
      rule.where=taint_parse_treet::rulet::THIS;
    }
    else if(std::string(where, 0, 9)=="parameter")
    {
      rule.where=taint_parse_treet::rulet::PARAMETER;
      rule.parameter_number=
        safe_string2unsigned(std::string(where, 9, std::string::npos));
    }
    else
    {
      messaget message(message_handler);
      message.error() << "taint rule must have \"where\""
                      << " which is \"return_value\" or \"this\" "
                      << "or \"parameter1\"..."
                      << messaget::eom;
      return true;
    }

    rule.taint = taint_spec["taint"].value;
    rule.message = taint_spec["message"].value;
    rule.id = taint_spec["id"].value;

    dest.rules.push_back(rule);
  }

  return false;
}

void taint_parse_treet::rulet::output(std::ostream &out) const
{
  if(!id.empty())
    out << id << ": ";

  switch(kind)
  {
  case SOURCE: out << "SOURCE "; break;
  case SINK: out << "SINK "; break;
  case SANITIZER: out << "SANITIZER "; break;
  }

  out << taint << " on ";

  switch(where)
  {
  case THIS: out << "this in " << function_identifier; break;
  case PARAMETER: out << "parameter " << parameter_number << " of "
                      << function_identifier; break;
  case RETURN_VALUE: out << "return value of " << function_identifier; break;
  }

  out << '\n';
}

void taint_parse_treet::output(std::ostream &out) const
{
  for(const auto &rule : rules)
    rule.output(out);
}
