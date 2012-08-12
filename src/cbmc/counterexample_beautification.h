/*******************************************************************\

Module: Counterexample Beautification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_H
#define CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_H

#include <namespace.h>

#include <goto-symex/symex_target_equation.h>

#include <solvers/flattening/bv_minimize.h>

#include "bv_cbmc.h"

class counterexample_beautificationt
{
public:
  virtual ~counterexample_beautificationt()
  {
  }

  void operator()(
    bv_cbmct &bv_cbmc,
    const symex_target_equationt &equation,
    const namespacet &ns);

protected:
  void get_minimization_list(
    const bv_cbmct &bv_cbmc,
    const symex_target_equationt &equation,        
    minimization_listt &minimization_list);

  void minimize(
    const exprt &expr,
    class prop_minimizet &prop_minimize);

  symex_target_equationt::SSA_stepst::const_iterator get_failed_claim(
    const bv_cbmct &bv_cbmc,
    const symex_target_equationt &equation);

  // the failed claim
  symex_target_equationt::SSA_stepst::const_iterator failed;
};

#endif
