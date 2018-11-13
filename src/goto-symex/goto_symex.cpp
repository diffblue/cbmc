/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/simplify_expr.h>

unsigned goto_symext::nondet_count=0;
unsigned goto_symext::dynamic_counter=0;

void goto_symext::do_simplify(exprt &expr)
{
  if(simplify_opt)
    simplify(expr, ns);
}

nondet_symbol_exprt build_symex_nondet(typet &type, unsigned &nondet_count)
{
  irep_idt identifier = "symex::nondet" + std::to_string(nondet_count++);
  nondet_symbol_exprt new_expr(identifier, type);
  return new_expr;
}
