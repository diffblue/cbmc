/*******************************************************************\

Module: Counterexample Beautification using Incremental SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_GREEDY_H
#define CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_GREEDY_H

#include <set>

#include <solvers/flattening/sat_minimizer.h>

#include "counterexample_beautification.h"

class counterexample_beautification_greedyt:
  public counterexample_beautificationt
{
public:
  typedef sat_minimizert solvert;

  void operator()(
    solvert &solver,
    bv_cbmct &bv_cbmc,
    symex_target_equationt &equation,
    const namespacet &ns);

protected:
  void beautify_guards(
    solvert &cnf,
    bv_cbmct &bv_cbmc,
    symex_target_equationt &equation,        
    const namespacet &ns);

  void beautify_values(
    solvert &solver,
    bv_cbmct &bv_cbmc,
    symex_target_equationt &equation,        
    const namespacet &ns);

  // this minimizes the absolute value
  void minimize(
    solvert &solver,
    bv_cbmct &bv_cbmc,
    const namespacet &ns,
    const exprt &expr,
    const typet &type,
    unsigned offset,
    unsigned bit_nr);
                
  void beautify_try(
    solvert &solver,
    literalt l,
    bool v);
                    
  unsigned get_max_width(const namespacet &ns, const typet &type);

  // the failed claim
  symex_target_equationt::SSA_stepst::const_iterator failed;

  // the currently best assignment
  std::vector<bool> assignment;
  
  void save_assignment(propt &prop);
  void restore_assignment(propt &prop);
};

#endif
