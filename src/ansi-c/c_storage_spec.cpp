/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>

#include "c_storage_spec.h"

/*******************************************************************\

Function: c_storage_spect::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_storage_spect::read(const typet &type)
{
  if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      read(*it);
  }
  else if(type.id()==ID_static)
    is_static=true;
  else if(type.id()==ID_thread_local)
    is_thread_local=true;
  else if(type.id()==ID_inline)
    is_inline=true;
  else if(type.id()==ID_extern)
    is_extern=true;
  else if(type.id()==ID_typedef)
    is_typedef=true;
  else if(type.id()==ID_register)
    is_register=true;
  else if(type.id()==ID_auto)
  {
    // ignore
  }
  else if(type.id()==ID_msc_declspec)
  {
    const exprt &as_expr=static_cast<const exprt &>(static_cast<const irept &>(type));
    forall_operands(it, as_expr)
      if(it->id()==ID_thread)
        is_thread_local=true;
  }
}
