/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

#include <util/namespace.h>

#include "fence.h"

bool is_fence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
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
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  return (instruction.is_function_call() && ns.lookup(
    to_code_function_call(instruction.code).function()).base_name == "lwfence")
    /* if assembly-sensitive algorithms are not available */
  || (instruction.is_other() && instruction.code.get_statement()==ID_fence
      && instruction.code.get_bool(ID_WWfence)
      && instruction.code.get_bool(ID_RWfence)
      && instruction.code.get_bool(ID_RRfence));
}
