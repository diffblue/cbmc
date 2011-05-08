/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_code.h>

#include "value_set_domain.h"

/*******************************************************************\

Function: value_set_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_domaint::transform(
  const namespacet &ns,
  locationt from_l,
  locationt to_l)
{
  switch(from_l->type)
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:    
    value_set.do_end_function(static_analysis_baset::get_return_lhs(to_l), ns);
    break;
  
  case RETURN:
  case OTHER:
  case ASSIGN:
  case DECL:
    value_set.apply_code(from_l->code, ns);
    break;
    
  case ASSUME:
    value_set.guard(from_l->guard, ns);
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code=
        to_code_function_call(from_l->code);

      value_set.do_function_call(to_l->function, code.arguments(), ns);
    }
    break;
  
  default:;
    // do nothing
  }
}
