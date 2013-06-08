/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <ansi-c/c_types.h>

#include "internal_additions.h"

/*******************************************************************\

Function: java_internal_additions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_internal_additions(symbol_tablet &dest)
{
  // add c::__CPROVER_rounding_mode

  {
    symbolt symbol;
    symbol.base_name="__CPROVER_rounding_mode";
    symbol.name="c::__CPROVER_rounding_mode";
    symbol.type=int_type();
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    dest.add(symbol);
  }

  // add c::__new
  // void *__new(__typeof__(sizeof(int)));

  {
    code_typet type;
    type.return_type()=pointer_typet(void_typet());
    type.parameters().resize(1);
    type.parameters()[0].type()=size_type();
  
    symbolt symbol;
    symbol.base_name="__new";
    symbol.name="c::__new";
    symbol.type=type;
    dest.add(symbol);
  }
}
