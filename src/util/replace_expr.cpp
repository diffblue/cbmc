/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "replace_expr.h"
#include "expr_iterator.h"

bool replace_expr(const exprt &what, const exprt &by, exprt &dest)
{
  bool no_change = true;

  for(auto it = dest.depth_begin(), itend = dest.depth_end();
      it != itend;) // no ++it
  {
    if(*it == what)
    {
      it.mutate() = by;
      no_change = false;
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  return no_change;
}

bool replace_expr(const replace_mapt &what, exprt &dest)
{
  bool no_change = true;

  for(auto it = dest.depth_begin(), itend = dest.depth_end();
      it != itend;) // No ++it
  {
    replace_mapt::const_iterator findit = what.find(*it);
    if(findit != what.end())
    {
      it.mutate() = findit->second;
      no_change = false;
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  return no_change;
}
