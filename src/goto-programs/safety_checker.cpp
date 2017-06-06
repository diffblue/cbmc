/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Safety Checker Interface

#include "safety_checker.h"

safety_checkert::safety_checkert(const namespacet &_ns):
  ns(_ns)
{
}

safety_checkert::safety_checkert(
  const namespacet &_ns,
  message_handlert &_message_handler):
  messaget(_message_handler),
  ns(_ns)
{
}
