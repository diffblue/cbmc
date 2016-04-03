/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/cprover_prefix.h>
#include <util/symbol_table.h>

#include <ansi-c/c_types.h>

#include "jsil_internal_additions.h"

/*******************************************************************\

Function: jsil_internal_additions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_internal_additions(symbol_tablet &dest)
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

  // add __CPROVER_malloc_object

  {
    symbolt symbol;
    symbol.base_name="__CPROVER_malloc_object";
    symbol.name=CPROVER_PREFIX "malloc_object";
    symbol.type=pointer_typet(empty_typet());
    symbol.mode=ID_C;
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    dest.add(symbol);
  }

  // add eval

  {
    code_typet eval_type;
    code_typet::parametert p;
    eval_type.parameters().push_back(p);

    symbolt symbol;
    symbol.base_name="eval";
    symbol.name="eval";
    symbol.type=eval_type;
    symbol.mode="jsil";
    dest.add(symbol);
  }
}
