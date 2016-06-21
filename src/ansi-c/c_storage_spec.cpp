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
  if(type.id()==ID_merged_type ||
     type.id()==ID_code)
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
  else if(type.id()==ID_weak)
    is_weak=true;
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
  else if(type.id()==ID_alias &&
          type.has_subtype() &&
          type.subtype().id()==ID_string_constant)
  {
    alias=type.subtype().get(ID_value);
  }
  else if(type.id()==ID_asm &&
          type.has_subtype() &&
          type.subtype().id()==ID_string_constant)
  {
    asm_label=type.subtype().get(ID_value);
  }
  else if(type.id()==ID_section &&
          type.has_subtype() &&
          type.subtype().id()==ID_string_constant)
  {
    section=type.subtype().get(ID_value);
  }
}
