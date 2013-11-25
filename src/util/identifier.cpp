/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>

#include "identifier.h"

/*******************************************************************\

Function: identifiert::as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string identifiert::as_string() const
{
  std::string result;

  for(componentst::const_iterator it=components.begin();
      it!=components.end(); it++)
  {
    if(it!=components.begin()) result+=ID_SEPARATOR;
    result+=*it;
  }

  return result;
}

/*******************************************************************\

Function: identifiert::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void identifiert::parse(const std::string &s)
{
  std::string component;

  for(unsigned i=0; i<s.size();)
  {
    for(; i<s.size(); i++)
    {
      if(strncmp(s.c_str()+i, ID_SEPARATOR, strlen(ID_SEPARATOR))==0)
      {
        i+=strlen(ID_SEPARATOR);
        break;
      }
      else
        component+=s[i];
    }

    components.push_back(component);
    component="";
  }  
}
