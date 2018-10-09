/*******************************************************************\

Module: Helper functions for k-induction and loop invariants

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Helper functions for k-induction and loop invariants

#include "loop_utils.h"

#include <util/std_expr.h>

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>

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

void build_havoc_code(
  const goto_programt::targett loop_head,
  const modifiest &modifies,
  goto_programt &dest)
{
  for(modifiest::const_iterator
      m_it=modifies.begin();
      m_it!=modifies.end();
      m_it++)
  {
    exprt lhs=*m_it;
    side_effect_expr_nondett rhs(lhs.type(), loop_head->source_location);

    goto_programt::targett t = dest.add(goto_programt::make_assignment(
      code_assignt(std::move(lhs), std::move(rhs)),
      loop_head->source_location));
    t->code.add_source_location()=loop_head->source_location;
  }
}

void get_modifies_lhs(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &lhs,
  modifiest &modifies)
{
  if(lhs.id()==ID_symbol)
    modifies.insert(lhs);
  else if(lhs.id()==ID_dereference)
  {
    modifiest m=local_may_alias.get(t, to_dereference_expr(lhs).pointer());
    for(modifiest::const_iterator m_it=m.begin();
        m_it!=m.end(); m_it++)
      get_modifies_lhs(local_may_alias, t, *m_it, modifies);
  }
  else if(lhs.id()==ID_member)
  {
  }
  else if(lhs.id()==ID_index)
  {
  }
  else if(lhs.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(lhs);

    get_modifies_lhs(local_may_alias, t, if_expr.true_case(), modifies);
    get_modifies_lhs(local_may_alias, t, if_expr.false_case(), modifies);
  }
}

void get_modifies(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  modifiest &modifies)
{
  for(loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction=**i_it;

    if(instruction.is_assign())
    {
      const exprt &lhs=to_code_assign(instruction.code).lhs();
      get_modifies_lhs(local_may_alias, *i_it, lhs, modifies);
    }
    else if(instruction.is_function_call())
    {
      const exprt &lhs=to_code_function_call(instruction.code).lhs();
      get_modifies_lhs(local_may_alias, *i_it, lhs, modifies);
    }
  }
}
