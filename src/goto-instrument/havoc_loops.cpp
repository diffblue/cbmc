/*******************************************************************\

Module: Havoc Loops

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>

#include "havoc_loops.h"

/*******************************************************************\

Function: havoc_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loops(goto_functionst::goto_functiont &goto_function)
{
  natural_loopst natural_loops;
  natural_loops(goto_function.body);
  local_may_aliast local_may_alias(goto_function);
}

/*******************************************************************\

Function: havoc_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void havoc_loops(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    havoc_loops(it->second);
}
