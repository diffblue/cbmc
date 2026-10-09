/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_exception_id.h"

#include <util/c_types.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/std_types.h>

/// turns a type into a list of relevant exception IDs
void cpp_exception_list_rec(
  const typet &src,
  const namespacet &ns,
  const std::string &suffix,
  std::vector<irep_idt> &dest)
{
  if(src.id() == ID_pointer)
  {
    // A C++ reference is represented as a pointer carrying ID_C_reference.
    // The pointee/referent type is the pointer's base type in both cases, so
    // extract it with to_pointer_type -- which is valid for a reference too,
    // whereas to_reference_type asserts ID_C_reference and would fail its
    // precondition on a genuine (non-reference) pointer such as the exception
    // type of `catch(T *)`.  Only the exception-id marker differs: a genuine
    // pointer type appends "_ptr" (matching how a thrown `T *` is catalogued),
    // a reference does not.
    const typet &base = to_pointer_type(src).base_type();
    if(src.get_bool(ID_C_reference))
    {
      // do not change
      cpp_exception_list_rec(base, ns, suffix, dest);
    }
    else
    {
      // append suffix _ptr
      cpp_exception_list_rec(base, ns, "_ptr" + suffix, dest);
    }
  }
  else if(src.id() == ID_union_tag)
  {
    cpp_exception_list_rec(ns.follow_tag(to_union_tag_type(src)), ns, suffix, dest);
  }
  else if(src.id()==ID_union)
  {
    // just get tag
    dest.push_back("union_"+src.get_string(ID_tag));
  }
  else if(src.id() == ID_struct_tag)
  {
    cpp_exception_list_rec(ns.follow_tag(to_struct_tag_type(src)), ns, suffix, dest);
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
