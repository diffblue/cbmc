/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/config.h>

#include "cpp_enum_type.h"

/*******************************************************************\

Function: cpp_enum_typet::cpp_enum_typet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_enum_typet::cpp_enum_typet():typet(ID_c_enum)
{
  set(ID_width, config.ansi_c.int_width);
}

/*******************************************************************\

Function: cpp_enum_typet::generate_anon_tag

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

irep_idt cpp_enum_typet::generate_anon_tag() const
{
  // This will only clash with anon enums that would have
  // clashes on the enum constants anyway.
  
  const irept::subt &b=body().get_sub();
  
  std::string result="#anonE";
  
  forall_irep(it, b)
  {
    result+="#";
    result+=id2string(it->get(ID_name));
  }
  
  return result;
}
