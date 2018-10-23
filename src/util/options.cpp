/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Options

#include "options.h"

#include "json.h"
#include "string2int.h"
#include "xml.h"

void optionst::set_option(const std::string &option,
                          const std::string &value)
{
  value_listt &value_list=option_map[option];
  value_list.clear();
  value_list.push_back(value);
}

void optionst::set_option(const std::string &option,
                          const bool value)
{
  set_option(option, std::string(value?"1":"0"));
}

void optionst::set_option(const std::string &option, const int value)
{
  set_option(option, std::to_string(value));
}

void optionst::set_option(const std::string &option, const unsigned value)
{
  set_option(option, std::to_string(value));
}

bool optionst::get_bool_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?false:(std::stoi(value)!=0);
}

signed int optionst::get_signed_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:std::stoi(value);
}

unsigned int optionst::get_unsigned_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:safe_string2unsigned(value);
}

bool optionst::is_set(const std::string &option) const
{
  return option_map.find(option) != option_map.end();
}

const std::string optionst::get_option(const std::string &option) const
{
  option_mapt::const_iterator it=
    option_map.find(option);

  if(it==option_map.end())
    return std::string();
  else if(it->second.empty())
    return std::string();
  else
    return it->second.front();
}

const optionst::value_listt &optionst::get_list_option(
  const std::string &option) const
{
  option_mapt::const_iterator it=
    option_map.find(option);

  if(it==option_map.end())
    return empty_list;
  else
    return it->second;
}

/// Returns the options as JSON key value pairs
json_objectt optionst::to_json() const
{
  json_objectt json_options;
  for(const auto &option_pair : option_map)
  {
    json_arrayt &values = json_options[option_pair.first].make_array();
    for(const auto &value : option_pair.second)
      values.push_back(json_stringt(value));
  }
  return json_options;
}

/// Returns the options in XML format
xmlt optionst::to_xml() const
{
  xmlt xml_options("options");
  for(const auto &option_pair : option_map)
  {
    xmlt &xml_option = xml_options.new_element("option");
    xml_option.set_attribute("name", option_pair.first);
    for(const auto &value : option_pair.second)
    {
      xmlt &xml_value = xml_option.new_element("value");
      xml_value.data = value;
    }
  }
  return xml_options;
}

/// Outputs the options to `out`
void optionst::output(std::ostream &out) const
{
  for(const auto &option_pair : option_map)
  {
    out << option_pair.first << ": ";
    bool first = true;
    for(const auto &value : option_pair.second)
    {
      if(first)
        first = false;
      else
        out << ", ";
      out << '"' << value << '"';
    }
    out << "\n";
  }
}
