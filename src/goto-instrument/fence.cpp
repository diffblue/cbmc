/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

#include "fence.h"

bool is_fence(
  goto_programt::instructiont instruction,
  contextt &context
)
{
  namespacet ns(context);

  return instruction.is_function_call()
    && ns.lookup(to_code_function_call(instruction.code).function()).base_name == "fence";
}

bool is_lwfence(
  goto_programt::instructiont instruction,
  contextt &context
)
{
  namespacet ns(context);

  return instruction.is_function_call()
    && ns.lookup(to_code_function_call(instruction.code).function()).base_name == "lwfence";
}
