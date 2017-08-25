/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

bool cpp_typecheckt::cpp_is_pod(const typet &type) const
{
  if(type.id()==ID_struct)
  {
    // Not allowed in PODs:
    // * Non-PODs
    // * Constructors/Destructors
    // * virtuals
    // * private/protected, unless static
    // * overloading assignment operator
    // * Base classes

    const struct_typet &struct_type=to_struct_type(type);

    if(!type.find(ID_bases).get_sub().empty())
      return false;

    const struct_typet::componentst &components=
      struct_type.components();

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_bool(ID_is_type))
        continue;

      if(it->get_base_name()=="operator=")
        return false;

      if(it->get_bool(ID_is_virtual))
        return false;

      const typet &sub_type=it->type();

      if(sub_type.id()==ID_code)
      {
        if(it->get_bool(ID_is_virtual))
          return false;

        const typet &return_type=to_code_type(sub_type).return_type();

        if(return_type.id()==ID_constructor ||
           return_type.id()==ID_destructor)
          return false;
      }
      else if(it->get(ID_access)!=ID_public &&
              !it->get_bool(ID_is_static))
        return false;

      if(!cpp_is_pod(sub_type))
        return false;
    }

    return true;
  }
  else if(type.id()==ID_array)
  {
    return cpp_is_pod(type.subtype());
  }
  else if(type.id()==ID_pointer)
  {
    if(is_reference(type)) // references are not PODs
      return false;

    // but pointers are PODs!
    return true;
  }
  else if(type.id()==ID_symbol)
  {
    const symbolt &symb=lookup(type.get(ID_identifier));
    assert(symb.is_type);
    return cpp_is_pod(symb.type);
  }

  // everything else is POD
  return true;
}
