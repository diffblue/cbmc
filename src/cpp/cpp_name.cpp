/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_name.h"

#include <cassert>
#include <sstream>

irep_idt cpp_namet::get_base_name() const
{
  const subt &sub=get_sub();

  // find last "::"
  std::size_t base=0;

  for(std::size_t i=0; i<sub.size(); i++)
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
      ss << location() << '\n';
      ss << "no template arguments allowed here";
      throw ss.str();
    }
    else
      name_component=it->id_string();

    identifier+=name_component;

    if(id=="::")
      base_name.clear();
    else
      base_name+=name_component;
  }
}
#endif

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
