/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Options

#include "options.h"

#include "string2int.h"

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
