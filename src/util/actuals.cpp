/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "actuals.h"

/*******************************************************************\

Function: get_actual_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_actual_map(const exprt &expr,
                    replace_symbolt &actual_map)
{
  forall_operands(it, expr)
  {
    if(it->id()!="actual" ||
       it->operands().size()!=1)
      throw "expected actual";

    const exprt &value=it->op0();
    const irep_idt &identifier=it->get(ID_identifier);

    if(value.id()==ID_type)
      actual_map.insert(identifier, value.type());
    else
      actual_map.insert(identifier, value);
  }
}

