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
  PRECONDITION(!loop.empty());

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
  get_assigns_lhs(
    local_may_alias, t, lhs, assigns, [](const exprt &e) { return true; });
}

void get_assigns_lhs(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &lhs,
  assignst &assigns,
  std::function<bool(const exprt &)> predicate)
{
  assignst new_assigns;

  // The targets built below from the may-alias information are new
  // expressions. Give them the source location of the assignment they come
  // from, as the instrumentation of the inferred write set relies on it.
  const source_locationt &location = lhs.source_location().is_not_nil()
                                       ? lhs.source_location()
                                       : t->source_location();

  if(lhs.id() == ID_symbol || lhs.id() == ID_index)
  {
    // All variables `v` and their indexing expressions `v[idx]` are assigns.
    new_assigns.insert(lhs);
  }
  else if(lhs.id() == ID_member)
  {
    auto op = to_member_expr(lhs).struct_op();
    auto component_name = to_member_expr(lhs).get_component_name();

    // Insert expressions of form `v.member`.
    if(op.id() == ID_symbol)
    {
      new_assigns.insert(lhs);
    }
    // For expressions of form `v->member`, insert all targets `u->member`,
    // where `u` and `v` alias.
    else if(op.id() == ID_dereference)
    {
      const pointer_arithmetict ptr(to_dereference_expr(op).pointer());
      for(const auto &mod : local_may_alias.get(t, ptr.pointer))
      {
        if(mod.id() == ID_unknown)
        {
          continue;
        }
        const exprt typed_mod =
          typecast_exprt::conditional_cast(mod, ptr.pointer.type());
        exprt to_insert;
        if(ptr.offset.is_nil())
        {
          // u->member
          to_insert = member_exprt(
            dereference_exprt{typed_mod}, component_name, lhs.type());
        }
        else
        {
          // (u+offset)->member
          to_insert = member_exprt(
            dereference_exprt{plus_exprt{typed_mod, ptr.offset}},
            component_name,
            lhs.type());
        }
        to_insert.add_source_location() = location;
        new_assigns.insert(to_insert);
      }
    }
  }
  else if(lhs.id() == ID_dereference)
  {
    // All dereference `*v` and their alias `*u` are assigns.
    const pointer_arithmetict ptr(to_dereference_expr(lhs).pointer());
    for(const auto &mod : local_may_alias.get(t, ptr.pointer))
    {
      if(mod.id() == ID_unknown)
      {
        continue;
      }
      const exprt typed_mod =
        typecast_exprt::conditional_cast(mod, ptr.pointer.type());
      exprt to_insert;
      if(ptr.offset.is_nil())
        to_insert = dereference_exprt{typed_mod};
      else
        to_insert = dereference_exprt{plus_exprt{typed_mod, ptr.offset}};
      to_insert.add_source_location() = location;
      new_assigns.insert(std::move(to_insert));
    }
  }
  else if(lhs.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(lhs);

    get_assigns_lhs(
      local_may_alias, t, if_expr.true_case(), assigns, predicate);
    get_assigns_lhs(
      local_may_alias, t, if_expr.false_case(), assigns, predicate);
  }

  std::copy_if(
    new_assigns.begin(),
    new_assigns.end(),
    std::inserter(assigns, assigns.begin()),
    predicate);
}

void get_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  assignst &assigns)
{
  get_assigns(
    local_may_alias, loop, assigns, [](const exprt &e) { return true; });
}

void get_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  assignst &assigns,
  std::function<bool(const exprt &)> predicate)
{
  for(loopt::const_iterator i_it = loop.begin(); i_it != loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction = **i_it;

    if(instruction.is_assign())
    {
      const exprt &lhs = instruction.assign_lhs();
      get_assigns_lhs(local_may_alias, *i_it, lhs, assigns, predicate);
    }
    else if(instruction.is_function_call())
    {
      const exprt &lhs = instruction.call_lhs();
      get_assigns_lhs(local_may_alias, *i_it, lhs, assigns, predicate);
    }
  }
}
