/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "safety_checker.h"

/*******************************************************************\

Function: safety_checkert::safety_checkert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::safety_checkert(const namespacet &_ns):
  ns(_ns)
{
}

/*******************************************************************\

Function: safety_checkert::safety_checkert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::safety_checkert(
  const namespacet &_ns,
  message_handlert &_message_handler):
  messaget(_message_handler),
  ns(_ns)
{
}

