/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "cpp_exception_id.h"

/*******************************************************************\

Function: cpp_exception_list_rec

  Inputs:

 Outputs:

 Purpose: turns a type into a list of relevant exception IDs

\*******************************************************************/

#include <iostream>

void cpp_exception_list_rec(
  const typet &src,
  const namespacet &ns,
  const std::string &suffix,
  std::vector<irep_idt> &dest)
{
  if(src.id()==ID_pointer)
  {
    if(src.get_bool(ID_C_reference))
    {
      // do not change
      cpp_exception_list_rec(src.subtype(), ns, suffix, dest);
      return;
    }
    else
    {
      // append suffix _ptr
      cpp_exception_list_rec(src.subtype(), ns, "_ptr"+suffix, dest);
      return;
    }
  }

  // grab C/C++ type
  irep_idt c_type=src.get(ID_C_c_type);
  
  if(c_type!=irep_idt())
  {
    dest.push_back(id2string(c_type)+suffix);
    return;
  }

  std::cout << "XX: " << src.pretty() << std::endl;
  
  return;
}

/*******************************************************************\

Function: cpp_exception_list

  Inputs:

 Outputs:

 Purpose: turns a type into a list of relevant exception IDs

\*******************************************************************/

irept cpp_exception_list(const typet &src, const namespacet &ns)
{
  std::vector<irep_idt> ids;
  irept result(ID_exception_list);
  
  cpp_exception_list_rec(src, ns, "", ids);
  result.get_sub().resize(ids.size());

  for(unsigned i=0; i<ids.size(); i++)
    result.get_sub()[i].id(ids[i]);
  
  return result;
}

/*******************************************************************\

Function: cpp_exception_id

  Inputs:

 Outputs:

 Purpose: turns a type into an exception ID

\*******************************************************************/

irep_idt cpp_exception_id(const typet &src, const namespacet &ns)
{
  std::vector<irep_idt> ids;
  cpp_exception_list_rec(src, ns, "", ids);
  assert(!ids.empty());
  return ids.front();
}
