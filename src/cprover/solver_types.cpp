/*******************************************************************\

Module: Solver Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver Types

#include "solver_types.h"

void framet::add_invariant(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_invariant(conjunct);
  }
  else
    invariants.push_back(std::move(invariant));
}

void framet::add_auxiliary(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_auxiliary(conjunct);
  }
  else
    auxiliaries.push_back(std::move(invariant));
}
