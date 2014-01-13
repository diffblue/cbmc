/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_HISTORY_H
#define CPROVER_PATH_SYMEX_HISTORY_H

#include <cassert>

#include <util/std_expr.h>

#include "loc_ref.h"

class path_symex_stept
{
public:
  unsigned thread_nr;
  typedef std::vector<loc_reft> pc_vectort;
  pc_vectort pc_vector;

  exprt guard, ssa_rhs;
  exprt full_lhs;
  symbol_exprt ssa_lhs;

  bool hidden; 
  
  path_symex_stept():
    guard(nil_exprt()),
    ssa_rhs(nil_exprt()),
    full_lhs(nil_exprt()),
    hidden(false)
  {
  }
  
  inline loc_reft pc() const
  {
    assert(thread_nr<pc_vector.size());
    return pc_vector[thread_nr];
  }
};

class decision_proceduret;

class path_symex_historyt
{
public:
  typedef std::vector<path_symex_stept> stepst;
  stepst steps;
  
  // output  
  void output(std::ostream &out) const;
  
  // interface to solvers
  void convert(decision_proceduret &dest) const;
};

static inline decision_proceduret &operator << (
  decision_proceduret &dest,
  const path_symex_historyt &src)
{
  src.convert(dest);
  return dest;
}

#endif
