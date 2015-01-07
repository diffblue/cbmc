/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/cprover_prefix.h>

#include <ansi-c/c_types.h>

#include "java_bytecode_internal_additions.h"

/*******************************************************************\

Function: java_internal_additions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_internal_additions(symbol_tablet &dest)
{
  // add __CPROVER_rounding_mode

  {
    symbolt symbol;
    symbol.base_name="__CPROVER_rounding_mode";
    symbol.name=CPROVER_PREFIX "rounding_mode";
    symbol.type=signed_int_type();
    symbol.mode=ID_C;
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    dest.add(symbol);
  }
}
