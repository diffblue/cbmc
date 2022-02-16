/*******************************************************************\

Module: Helper functions for k-induction and loop invariants

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Helper functions for k-induction and loop invariants

#include "loop_utils.h"

#include <analyses/local_may_alias.h>

#include <goto-programs/pointer_arithmetic.h>

#include <util/pointer_expr.h>
#include <util/std_expr.h>

goto_programt::targett get_loop_exit(const loopt &loop)
{
  assert(!loop.empty());

  // find the last instruction in the loop
  std::map<unsigned, goto_programt::targett> loop_map;

  for(loopt::const_iterator l_it=loop.begin();
      l_it!=loop.end();
      l_it++)
    loop_map[(*l_it)->location_number]=*l_it;

  // get the one with the highest number
  goto_programt::targett last=(--loop_map.end())->second;

  return ++last;
}

void get_assigns_lhs(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &lhs,
  assignst &assigns)
{
  if(lhs.id() == ID_symbol || lhs.id() == ID_member || lhs.id() == ID_index)
    assigns.insert(lhs);
  else if(lhs.id()==ID_dereference)
  {
    const pointer_arithmetict ptr(to_dereference_expr(lhs).pointer());
    for(const auto &mod : local_may_alias.get(t, ptr.pointer))
    {
      const typecast_exprt typed_mod{mod, ptr.pointer.type()};
      if(mod.id() == ID_unknown)
      {
        throw analysis_exceptiont("Alias analysis returned UNKNOWN!");
      }
      if(ptr.offset.is_nil())
        assigns.insert(dereference_exprt{typed_mod});
      else
        assigns.insert(dereference_exprt{plus_exprt{typed_mod, ptr.offset}});
    }
  }
  else if(lhs.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(lhs);

    get_assigns_lhs(local_may_alias, t, if_expr.true_case(), assigns);
    get_assigns_lhs(local_may_alias, t, if_expr.false_case(), assigns);
  }
}

void get_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  assignst &assigns)
{
  for(loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction=**i_it;

    if(instruction.is_assign())
    {
      const exprt &lhs = instruction.assign_lhs();
      get_assigns_lhs(local_may_alias, *i_it, lhs, assigns);
    }
    else if(instruction.is_function_call())
    {
      const exprt &lhs = instruction.call_lhs();
      get_assigns_lhs(local_may_alias, *i_it, lhs, assigns);
    }
  }
}
