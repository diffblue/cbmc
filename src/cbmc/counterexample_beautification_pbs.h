/*******************************************************************\

Module: Counterexample Beautification using PBS

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_PBS_H
#define CPROVER_CBMC_COUNTEREXAMPLE_BEAUTIFICATION_PBS_H

#include <set>

#include <solvers/sat/pbs_dimacs_cnf.h>

#include "counterexample_beautification.h"

class counterexample_beautification_pbst:
  public counterexample_beautificationt
{
public:
  void counterexample_beautification(
    cnf_clause_listt &cnf,
    bv_cbmct &bv_cbmc,
    symex_target_equationt &equation,
    const namespacet &ns);

protected:
  void beautify(
    pbs_dimacs_cnft &pbs,
    bv_cbmct &bv_cbmc,
    const namespacet &ns,
    const exprt &expr,
    const typet &type,
    unsigned offset);
                
  void counterexample_beautification_guards(
    cnf_clause_listt &cnf,
    bv_cbmct &bv_cbmc,
    symex_target_equationt &equation,
    const namespacet &ns);

  void counterexample_beautification_values(
    cnf_clause_listt &cnf,
    bv_cbmct &bv_cbmc,
    symex_target_equationt &equation,
    const namespacet &ns);

  void setup_pbs(
    const cnf_clause_listt &cnf,
    pbs_dimacs_cnft &pbs);

  void run_pbs(pbs_dimacs_cnft &pbs);

  typedef std::list<bvt> guard_constraintst;
  guard_constraintst guard_constraints;

  symex_target_equationt::SSA_stepst::const_iterator failed;
};

#endif
