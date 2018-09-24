/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_declarator.h"

#include <ansi-c/merged_type.h>

#include <ostream>
#include <cassert>

void cpp_declaratort::output(std::ostream &out) const
{
  out << "  name: " << name().pretty() << "\n";
  out << "  type: " << type().pretty() << "\n";
  out << "  value: " << value().pretty() << "\n";
  out << "  init_args: " << init_args().pretty() << "\n";
  out << "  method_qualifier: " << method_qualifier().pretty() << "\n";
}

typet cpp_declaratort::merge_type(const typet &declaration_type) const
{
  typet dest_type=type();

  if(declaration_type.id()=="cpp-cast-operator")
    return dest_type;

  typet *p=&dest_type;

  // walk down subtype until we hit nil
  while(true)
  {
    typet &t=*p;
    if(t.is_nil())
    {
      t=declaration_type;
      break;
    }
    else if(t.id()==ID_merged_type)
    {
      // the chain continues with the last one
      auto &merged_type = to_merged_type(t);
      p = &merged_type.last_type();
    }
    else
    {
      assert(!t.id().empty());
      p=&t.subtype();
    }
  }

  return dest_type;
}
