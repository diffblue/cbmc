/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_exception_id.h"

#include <util/invariant.h>
#include <util/std_types.h>

/// turns a type into a list of relevant exception IDs
void cpp_exception_list_rec(
  const typet &src,
  const namespacet &ns,
  const std::string &suffix,
  std::vector<irep_idt> &dest)
{
  if(src.id() == ID_symbol_type)
  {
    cpp_exception_list_rec(ns.follow(src), ns, suffix, dest);
  }
  else if(src.id()==ID_pointer)
  {
    if(src.get_bool(ID_C_reference))
    {
      // do not change
      cpp_exception_list_rec(src.subtype(), ns, suffix, dest);
    }
    else
    {
      // append suffix _ptr
      cpp_exception_list_rec(src.subtype(), ns, "_ptr"+suffix, dest);
    }
  }
  else if(src.id()==ID_union)
  {
    // just get tag
    dest.push_back("union_"+src.get_string(ID_tag));
  }
  else if(src.id()==ID_struct)
  {
    // just get tag
    dest.push_back("struct_"+src.get_string(ID_tag));

    // now do any bases, recursively
    for(const auto &b : to_struct_type(src).bases())
      cpp_exception_list_rec(b.type(), ns, suffix, dest);
  }
  else
  {
    // grab C/C++ type
    irep_idt c_type=src.get(ID_C_c_type);

    if(!c_type.empty())
    {
      dest.push_back(id2string(c_type)+suffix);
      return;
    }
  }
}

/// turns a type into a list of relevant exception IDs
irept cpp_exception_list(
  const typet &src,
  const namespacet &ns)
{
  std::vector<irep_idt> ids;
  irept result(ID_exception_list);

  cpp_exception_list_rec(src, ns, "", ids);
  result.get_sub().resize(ids.size());

  for(std::size_t i=0; i<ids.size(); i++)
    result.get_sub()[i].id(ids[i]);

  return result;
}

/// turns a type into an exception ID
irep_idt cpp_exception_id(
  const typet &src,
  const namespacet &ns)
{
  std::vector<irep_idt> ids;
  cpp_exception_list_rec(src, ns, "", ids);
  CHECK_RETURN(!ids.empty());
  return ids.front();
}
