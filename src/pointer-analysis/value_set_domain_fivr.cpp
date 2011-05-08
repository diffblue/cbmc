/*******************************************************************\

Module: Value Set Domain (Flow Insensitive, Sharing, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#include <std_code.h>

#include "value_set_domain_fivr.h"

/*******************************************************************\

Function: value_set_domain_fivrt::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_domain_fivrt::transform(
  const namespacet &ns,
  locationt from_l,
  locationt to_l)
{   
  value_set.set_from(from_l->function, from_l->location_number);
  value_set.set_to(to_l->function, to_l->location_number);
  
  #if 0
  std::cout << "Transforming: " << 
    from_l->function << " " << from_l->location_number << " to " << 
    to_l->function << " " << to_l->location_number << std::endl;
  #endif
  
  switch(from_l->type)
  {
  case END_FUNCTION:    
    value_set.do_end_function(get_return_lhs(to_l), ns);
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
      break;        
    }
    
  default:;    
  }
  
  return value_set.handover();
}
