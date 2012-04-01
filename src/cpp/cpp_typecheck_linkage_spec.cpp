/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert(cpp_linkage_spect &linkage_spec)
{
  irep_idt old_linkage_spec=current_linkage_spec;

  current_linkage_spec=linkage_spec.linkage().get(ID_value);
  
  // there is a linkage spec "C++", which we know as "cpp"
  if(current_linkage_spec=="C++")
    current_linkage_spec=ID_cpp;

  // do the declarations
  for(cpp_linkage_spect::itemst::iterator
      it=linkage_spec.items().begin();
      it!=linkage_spec.items().end();
      it++)
    convert(*it);

  // back to previous linkage spec
  current_linkage_spec=old_linkage_spec;
}
