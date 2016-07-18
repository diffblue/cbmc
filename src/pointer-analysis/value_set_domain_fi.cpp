/*******************************************************************\

Module: Value Set Domain (Flow Insensitive)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#include <util/std_code.h>

#include "value_set_domain_fi.h"
#include "value_set_domain.h"

/*******************************************************************\

Function: value_set_domain_fit::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_domain_fit::transform(
  locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns)
{ 
  value_set.changed = false;
  
  value_set.set_from(from_l->function, from_l->location_number);
  value_set.set_to(to_l->function, to_l->location_number);
  
//  std::cout << "transforming: " << 
//      from_l->function << " " << from_l->location_number << " to " << 
//      to_l->function << " " << to_l->location_number << std::endl;
  
  switch(from_l->type)
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:    
    value_set.do_end_function(value_set_domaint::get_return_lhs(to_l), ns);
    break;
  
  case RETURN:
  case OTHER:
  case ASSIGN:
    value_set.apply_code(from_l->code, ns);
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
