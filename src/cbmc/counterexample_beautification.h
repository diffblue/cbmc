/*******************************************************************\

Module: Counterexample Beautification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_H
#define CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_H

#include <namespace.h>
#include <solvers/sat/cnf_clause_list.h>
#include <goto-symex/symex_target_equation.h>

#include "bv_cbmc.h"

class counterexample_beautificationt
{
public:
  virtual ~counterexample_beautificationt()
  {
  }

protected:
  typedef std::set<exprt> minimization_symbolst;

  void get_minimization_symbols(
    const bv_cbmct &bv_cbmc,
    const symex_target_equationt &equation,        
    const symex_target_equationt::SSA_stepst::const_iterator failed,
    minimization_symbolst &minimization_symbols);

  symex_target_equationt::SSA_stepst::const_iterator get_failed_claim(
    const bv_cbmct &bv_cbmc,
    const symex_target_equationt &equation);
};

#endif
