/*******************************************************************\

Module: Symbolic execution, struct flattening

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic execution, struct flattening

#include "goto_symex.h"

#include <iostream>

void goto_symext::flatten_structs(exprt &dest)
{
  for(auto &op : dest.operands())
    flatten_structs(op);

  if(dest.id()==ID_member)
  {
    exprt &op=to_member_expr(dest).compound();

    if(op.id()==ID_symbol)
    {
      symbol_exprt tmp=to_symbol_expr(op);
      irep_idt new_id=id2string(tmp.get_identifier())+'.'+
                      id2string(to_member_expr(dest).get_component_name());
      tmp.set_identifier(new_id);
      tmp.type()=dest.type();
      dest=tmp;
    }
    else if(op.id()==ID_index)
    {
    }
    else if(op.id()==ID_if)
    {
    }
    else
    {
      throw "can't flatten member in "+op.id_string();
    }
  }
}
