/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_REWRITE_UNION_H
#define CPROVER_GOTO_SYMEX_REWRITE_UNION_H

#include <util/expr.h>
#include <util/namespace.h>

void rewrite_union(
  exprt &expr,
  const namespacet &ns);

#endif // CPROVER_GOTO_SYMEX_REWRITE_UNION_H
