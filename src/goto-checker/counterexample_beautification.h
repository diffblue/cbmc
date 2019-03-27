/*******************************************************************\

Module: Counterexample Beautification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Counterexample Beautification

#ifndef CPROVER_GOTO_CHECKER_COUNTEREXAMPLE_BEAUTIFICATION_H
#define CPROVER_GOTO_CHECKER_COUNTEREXAMPLE_BEAUTIFICATION_H

#include <util/namespace.h>

#include <goto-symex/symex_target_equation.h>

#include <solvers/flattening/bv_minimize.h>

class counterexample_beautificationt
{
public:
  explicit counterexample_beautificationt(message_handlert &message_handler);
  virtual ~counterexample_beautificationt() = default;

  void operator()(boolbvt &boolbv, const symex_target_equationt &equation);

protected:
  void get_minimization_list(
    decision_proceduret &decision_procedure,
    const symex_target_equationt &equation,
    minimization_listt &minimization_list);

  void minimize(const exprt &expr, class prop_minimizet &prop_minimize);

  symex_target_equationt::SSA_stepst::const_iterator get_failed_property(
    const decision_proceduret &decision_procedure,
    const symex_target_equationt &equation);

  // the failed property
  symex_target_equationt::SSA_stepst::const_iterator failed;

  messaget log;
};

#endif // CPROVER_GOTO_CHECKER_COUNTEREXAMPLE_BEAUTIFICATION_H
