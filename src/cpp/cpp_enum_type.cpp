/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_enum_type.h"

cpp_enum_typet::cpp_enum_typet():typet(ID_c_enum)
{
}

irep_idt cpp_enum_typet::generate_anon_tag() const
{
  // This will only clash with anon enums that would have
  // clashes on the enum constants anyway.

  const irept::subt &b=body().get_sub();

  std::string result="#anonE";

  for(const auto &value : b)
  {
    result+='#';
    result += id2string(value.get(ID_name));
  }

  return result;
}
