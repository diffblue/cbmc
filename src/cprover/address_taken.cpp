/*******************************************************************\

Module: Address Taken

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Address Taken

#include "address_taken.h"

#include <util/pointer_expr.h>

#include "state.h"

// we look for ❝x❞ that's
// * not the argument of ς(...), i.e., evaluate
// * not the argument of enter_scope_state(?, ?)
// * not the argument of exit_scope_state(?, ?)
// * not on the lhs of [...:=...]
static void find_objects_rec(
  const exprt &src,
  std::unordered_set<symbol_exprt, irep_hash> &result)
{
  if(src.id() == ID_object_address)
    result.insert(to_object_address_expr(src).object_expr());
  else if(src.id() == ID_evaluate)
  {
  }
  else if(src.id() == ID_enter_scope_state)
  {
  }
  else if(src.id() == ID_exit_scope_state)
  {
  }
  else if(src.id() == ID_update_state)
  {
    const auto &update_state_expr = to_update_state_expr(src);
    find_objects_rec(update_state_expr.new_value(), result);
  }
  else
  {
    for(auto &op : src.operands())
      find_objects_rec(op, result);
  }
}

std::unordered_set<symbol_exprt, irep_hash>
address_taken(const std::vector<exprt> &src)
{
  std::unordered_set<symbol_exprt, irep_hash> result;

  for(auto &expr : src)
    find_objects_rec(expr, result);

  return result;
}
