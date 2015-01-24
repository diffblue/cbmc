/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "i2string.h"
#include "string2int.h"
#include "options.h"

/*******************************************************************\

Function: optionst::set_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void optionst::set_option(const std::string &option,
                          const std::string &value)
{
  value_listt &value_list=option_map[option];
  value_list.clear();
  value_list.push_back(value);
}

/*******************************************************************\

Function: optionst::set_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void optionst::set_option(const std::string &option,
                          const bool value)
{
  set_option(option, std::string(value?"1":"0"));
}

/*******************************************************************\

Function: optionst::set_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void optionst::set_option(const std::string &option,
                          const signed int value)
{
  set_option(option, i2string(value));
}

/*******************************************************************\

Function: optionst::set_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void optionst::set_option(const std::string &option,
                          const unsigned int value)
{
  set_option(option, i2string(value));
}

/*******************************************************************\

Function: optionst::get_bool_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool optionst::get_bool_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?false:(safe_string2int(value)!=0);
}

/*******************************************************************\

Function: optionst::get_signed_int_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

signed int optionst::get_signed_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:safe_string2int(value);
}

/*******************************************************************\

Function: optionst::get_unsigned_int_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned int optionst::get_unsigned_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:safe_string2unsigned(value);
}

/*******************************************************************\

Function: optionst::get_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: optionst::get_list_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
