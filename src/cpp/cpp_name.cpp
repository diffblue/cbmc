/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <assert.h>

#include <sstream>

#include "cpp_name.h"

/*******************************************************************\

Function: cpp_namet::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_namet::convert(
  std::string &identifier,
  std::string &base_name) const
{
  forall_irep(it, get_sub())
  {
    const irep_idt id=it->id();

    std::string name_component;

    if(id==ID_name)
      name_component=it->get_string(ID_identifier);
    else if(id==ID_template_args)
    {
      std::stringstream ss;
      ss << location() << std::endl;
      ss << "no template arguments allowed here";
      throw ss.str();
    }
    else
      name_component=it->id_string();

    identifier+=name_component;

    if(id=="::")
      base_name="";
    else
      base_name+=name_component;
  }
}

/*******************************************************************\

Function: cpp_namet::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_namet::to_string() const
{
  std::string str;

  forall_irep(it, get_sub())
  {
    if(it->id()=="::")
      str += it->id_string();
    else if(it->id()==ID_template_args)
      str += "<...>";
    else
      str+=it->get_string(ID_identifier);
  }
  
  return str;
}
