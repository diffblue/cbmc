/*******************************************************************\

Module: Find Variables

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Find Variables

#include "find_variables.h"

#include <util/pointer_expr.h>

#include "state.h"

static void find_variables_rec(
  const exprt &src,
  std::unordered_set<symbol_exprt, irep_hash> &result)
{
  if(src.id() == ID_object_address)
    result.insert(to_object_address_expr(src).object_expr());
  else
  {
    for(auto &op : src.operands())
      find_variables_rec(op, result);
  }
}

std::unordered_set<symbol_exprt, irep_hash>
find_variables(const std::vector<exprt> &src)
{
  std::unordered_set<symbol_exprt, irep_hash> result;

  for(auto &expr : src)
    find_variables_rec(expr, result);

  return result;
}
