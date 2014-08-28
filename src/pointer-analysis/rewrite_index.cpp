/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "rewrite_index.h"

/*******************************************************************\

Function: rewrite_index

  Inputs:

 Outputs:

 Purpose: rewrite a[i] to *(a+i)

\*******************************************************************/

dereference_exprt rewrite_index(const index_exprt &index_expr)
{
  dereference_exprt result;
  result.pointer()=plus_exprt(index_expr.array(), index_expr.index());
  result.type()=index_expr.type();
  result.add_source_location()=index_expr.source_location();
  return result;
}
