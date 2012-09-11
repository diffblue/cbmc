/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <string2int.h>

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
  std::pair<option_mapt::iterator, bool>
    result=option_map.insert(option_mapt::value_type(option, value));

  if(!result.second) result.first->second=value;
}

/*******************************************************************\

Function: optionst::set_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void optionst::set_option(const std::string &option,
                          const char *value)
{
  set_option(option, std::string(value));
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
                          const int value)
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
  return value.empty()?false:safe_str2int(value.c_str());
}

/*******************************************************************\

Function: optionst::get_int_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int optionst::get_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:safe_str2int(value.c_str());
}

/*******************************************************************\

Function: optionst::get_option

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string optionst::get_option(const std::string &option) const
{
  std::map<std::string, std::string>::const_iterator it=
    option_map.find(option);

  if(it!=option_map.end()) return it->second;

  return "";
}

