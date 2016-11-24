/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <cassert>
#include <sstream>

#include "cpp_name.h"

/*******************************************************************\

Function: cpp_namet::get_base_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt cpp_namet::get_base_name() const
{
  const subt &sub=get_sub();
  
  // find last "::"
  unsigned base=0;

  for(unsigned i=0; i<sub.size(); i++)
  {
    if(sub[i].id()=="::")
      base=i+1;
  }

  if(base>=sub.size())
    return irep_idt();

  if(sub[base].id()==ID_name)
    return sub[base].get(ID_identifier);
  else if(base+1<sub.size() && sub[base].id()==ID_operator)
    return "operator"+sub[base+1].id_string();
  else if(base+1<sub.size() && sub[base].id()=="~" && sub[base+1].id()==ID_name)
    return "~"+sub[base+1].get_string(ID_identifier); 

  return irep_idt();
}

/*******************************************************************\

Function: cpp_namet::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
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
#endif

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
