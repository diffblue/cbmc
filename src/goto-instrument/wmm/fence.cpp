/*******************************************************************\

Module: Fences for instrumentation

Author: Vincent Nimal

Date: February 2012

\*******************************************************************/

/// \file
/// Fences for instrumentation

#include "fence.h"

#include <util/namespace.h>
#include <util/symbol.h>

bool is_fence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  return (instruction.is_function_call() &&
          ns.lookup(to_symbol_expr(instruction.call_function())).base_name ==
            "fence")
         /* if assembly-sensitive algorithms are not available */
         || (instruction.is_other() &&
             instruction.code().get_statement() == ID_fence &&
             instruction.code().get_bool(ID_WWfence) &&
             instruction.code().get_bool(ID_WRfence) &&
             instruction.code().get_bool(ID_RWfence) &&
             instruction.code().get_bool(ID_RRfence));
}

bool is_lwfence(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  return (instruction.is_function_call() &&
          ns.lookup(to_symbol_expr(instruction.call_function())).base_name ==
            "lwfence")
         /* if assembly-sensitive algorithms are not available */
         || (instruction.is_other() &&
             instruction.code().get_statement() == ID_fence &&
             instruction.code().get_bool(ID_WWfence) &&
             instruction.code().get_bool(ID_RWfence) &&
             instruction.code().get_bool(ID_RRfence));
}
