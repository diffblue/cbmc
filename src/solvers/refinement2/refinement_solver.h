/*******************************************************************\

Module: Model Refinement Loop

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Model Refinement Loop

#ifndef CPROVER_SOLVERS_REFINEMENT2_REFINEMENT_SOLVER_H
#define CPROVER_SOLVERS_REFINEMENT2_REFINEMENT_SOLVER_H

#include <solvers/flattening/boolbv.h>

class refinement_solver2t : public boolbvt
{
public:
  refinement_solver2t(const namespacet &, propt &, message_handlert &);

  decision_proceduret::resultt dec_solve() override;

  std::string decision_procedure_text() const override
  {
    return "refinement loop with "+prop.solver_text();
  }

protected:
  enum class refinement_resultt
  {
    CONSISTENT,
    REFINED,
    ERROR
  };

  refinement_resultt model_refinement();
  refinement_resultt refine_quantifier(const quantifiert &);

  bool existential(const quantifiert &) const;
  bool universal(const quantifiert &) const;
};

#endif // CPROVER_SOLVERS_REFINEMENT2_REFINEMENT_SOLVER_H
