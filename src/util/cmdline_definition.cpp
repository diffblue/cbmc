/*******************************************************************\

Module: Command line parsing

Author: Peter Schrammel

\*******************************************************************/

// \file Command line options definition

#include "cmdline_definition.h"

#include <sstream>

#include <util/invariant.h>
#include <util/json.h>
#include <util/xml.h>

cmdline_optiont::cmdline_optiont(
  std::string name,
  optionalt<argumentt> argument,
  std::string help_text,
  std::string option_group,
  optionalt<std::string> deprecated)
  : name(name),
    argument(argument),
    help_text(help_text),
    option_group(option_group),
    deprecated(deprecated)
{
}

cmdline_optiont::argumentt::argumentt(std::string name, std::string type)
  : name(name), type(type)
{
}

cmdline_definitiont::cmdline_definitiont(
  std::initializer_list<cmdline_optiont> &&initializer_list)
  : cmdline_options(initializer_list)
{
}

void cmdline_definitiont::concat(const cmdline_definitiont &other)
{
  cmdline_options.insert(
    cmdline_options.end(),
    other.cmdline_options.begin(),
    other.cmdline_options.end());
}

std::string cmdline_definitiont::to_help_text(
  std::size_t option_width,
  std::size_t total_width) const
{
  std::ostringstream os;
  std::string option_group;
  for(const auto &option : cmdline_options)
  {
    // do not print deprecated options
    if(option.deprecated.has_value())
      continue;

    // print option group at the start of a new grouop
    if(option.option_group != option_group)
    {
      option_group = option.option_group;
      os << '\n' << option_group << ":\n";
    }

    // print option with optional argument and auto-wrap help text
    std::string option_text = option.name;
    if(option.name.size() == 1)
      option_text = " -" + option_text;
    else
      option_text = " --" + option_text;
    if(option.argument.has_value())
      option_text += " " + option.argument->name;
    os << option_text;
    std::size_t padding = option_width;
    if(option_text.size() < option_width)
      padding = option_width - (option_text.size());
    else
      os << '\n';
    std::size_t index = 0;
    do
    {
      os << std::string(padding, ' ')
         << option.help_text.substr(index, total_width - option_width)
         << '\n';
      padding = option_width;
      index += total_width - option_width;
    } while(index < option.help_text.size() - 1);
  }
  return os.str();
}

std::string cmdline_definitiont::to_option_string() const
{
  std::ostringstream os;
  for(const auto &option : cmdline_options)
    os << "(" + option.name + ")" + (option.argument.has_value() ? ":" : "");
  return os.str();
}

json_arrayt cmdline_definitiont::to_json() const
{
  json_arrayt json_array;
  for(const auto &option : cmdline_options)
  {
    json_objectt json_option;
    json_option["name"] = json_stringt(option.name);
    json_option["helpText"] = json_stringt(option.help_text);
    json_option["optionGroup"] = json_stringt(option.option_group);
    if(option.argument.has_value())
    {
      json_objectt &json_argument = json_option["argument"].make_object();
      json_argument["name"] = json_stringt(option.argument->name);
      json_argument["type"] = json_stringt(option.argument->type);
    }
    if(option.deprecated.has_value())
    {
      json_option["deprecated"] = json_stringt(*option.deprecated);
    }
    json_array.push_back(std::move(json_option));
  }
  return json_array;
}

xmlt cmdline_definitiont::to_xml() const
{
  xmlt xml_cmdline("commandline");
  for(const auto &option : cmdline_options)
  {
    xmlt &xml_option = xml_cmdline.new_element("option");
    xml_option.set_attribute("name", option.name);
    xml_option.new_element("help_text").data = option.help_text;
    xml_option.new_element("option_group").data = option.option_group;
    if(option.argument.has_value())
    {
      xmlt &xml_argument = xml_option.new_element("argument");
      xml_argument.set_attribute("name", option.argument->name);
      xml_argument.set_attribute("type", option.argument->type);
    }
    if(option.deprecated.has_value())
    {
      xml_option.new_element("deprecated").data = *option.deprecated;
    }
  }
  return xml_cmdline;
}

cmdline_definitiont
operator+(cmdline_definitiont first, const cmdline_definitiont &second)
{
  first.concat(second);
  return first;
}
