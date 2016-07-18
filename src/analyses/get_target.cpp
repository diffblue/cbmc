/*******************************************************************\

Module: Get goto program target from location number or regex

Author: Daniel Poetzl

\*******************************************************************/

#include "get_target.h"

#include <regex>
#include <iostream>
#include <sstream>

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

get_targett::rest get_targett::from_location_number(
  unsigned location_number)
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;
    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->location_number==location_number)
      {
        return std::make_pair(true, i_it);
      }
    }
  }

  return std::make_pair(false, locationt());
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

get_targett::rest get_targett::from_location_number_string(
  const std::string &s)
{
  unsigned loc=unsafe_string2unsigned(s);
  return from_location_number(loc);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

get_targett::rest get_targett::from_regex(
  const std::string &regex,
  const bool first)
{
  if(regex.empty())
    return std::make_pair(false, locationt());

  std::regex r(regex);
  bool found=false;
  locationt l=locationt();

#if 0
  std::cout << "Regex: " << regex << std::endl;
#endif

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;
    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      std::ostringstream sstream;
      goto_program.output_instruction(ns, f_it->first, sstream, i_it);
      const std::string &s=sstream.str();

      bool b=std::regex_search(s, r);

      if(b)
      {
        if(first)
        {
          return std::make_pair(true, i_it);
        }
        if(found)
        {
          return std::make_pair(false, locationt());
        }
        l=i_it;
        found=true;
      }
    }
  }

  return std::make_pair(found, l);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

get_targett::rest get_targett::from_spec(
  const std::string &spec,
  bool first)
{
  if(spec.empty())
    return std::make_pair(false, locationt());

  if(spec[0]=='r')
  {
    const std::string &regex = spec.substr(1, std::string::npos);
    return from_regex(regex, first);
  }
  else
  {
    return from_location_number_string(spec);
  }
}
