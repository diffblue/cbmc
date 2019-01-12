/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#include "rewrite_index.h"

#include <util/std_expr.h>

/// rewrite a[i] to *(a+i)
dereference_exprt rewrite_index(const index_exprt &index_expr)
{
  dereference_exprt result(
    plus_exprt(index_expr.array(), index_expr.index()), index_expr.type());
  result.add_source_location()=index_expr.source_location();
  return result;
}
