/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

#include "fence.h"
#include <iostream>

bool is_fence(
  goto_programt::instructiont instruction,
  namespacet &ns)
{
  return (instruction.is_function_call() && ns.lookup(
    to_code_function_call(instruction.code).function()).base_name == "fence")
    /* if assembly-sensitive algorithms are not available */
    || (instruction.is_other() && instruction.code.get_statement()==ID_fence
      && instruction.code.get_bool(ID_WWfence)
      && instruction.code.get_bool(ID_WRfence)
      && instruction.code.get_bool(ID_RWfence)
      && instruction.code.get_bool(ID_RRfence));
}

bool is_lwfence(
  goto_programt::instructiont instruction,
  namespacet &ns)
{
  return (instruction.is_function_call() && ns.lookup(
    to_code_function_call(instruction.code).function()).base_name == "lwfence")
    /* if assembly-sensitive algorithms are not available */
  || (instruction.is_other() && instruction.code.get_statement()==ID_fence
      && instruction.code.get_bool(ID_WWfence)
      && instruction.code.get_bool(ID_RWfence)
      && instruction.code.get_bool(ID_RRfence));
}
