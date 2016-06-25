/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_REWRITE_UNION_H
#define CPROVER_GOTO_SYMEX_REWRITE_UNION_H

#include <goto-programs/goto_functions.h>

class exprt;
class namespacet;
class goto_functionst;
class goto_modelt;

void rewrite_union(
  exprt &expr,
  const namespacet &ns);

void rewrite_union(
  goto_functionst &goto_functions,
  const namespacet &ns);
void rewrite_union(goto_modelt &goto_model);

#endif // CPROVER_GOTO_SYMEX_REWRITE_UNION_H
