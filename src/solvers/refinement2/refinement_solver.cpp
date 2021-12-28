/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "refinement_solver.h"

#include <util/format_expr.h>

refinement_solver2t::refinement_solver2t(
  const namespacet &ns,
  propt &prop,
  message_handlert &message_handler)
  : boolbvt(ns, prop, message_handler)
{
}

decision_proceduret::resultt refinement_solver2t::dec_solve()
{
  // post-processing isn't incremental yet
  if(!post_processing_done)
  {
    const auto post_process_start = std::chrono::steady_clock::now();

    log.statistics() << "Post-processing" << messaget::eom;
    finish_eager_conversion();
    post_processing_done = true;

    const auto post_process_stop = std::chrono::steady_clock::now();
    std::chrono::duration<double> post_process_runtime =
      std::chrono::duration<double>(post_process_stop - post_process_start);
    log.status() << "Runtime Post-process: " << post_process_runtime.count()
                 << "s" << messaget::eom;
  }

  log.statistics() << "Solving with " << prop.solver_text() << messaget::eom;

  // we now enter the model refinement loop
  while(true)
  {
    switch(prop.prop_solve())
    {
    case propt::resultt::P_SATISFIABLE:
      // the model may need to be refined
      switch(model_refinement())
      {
      case refinement_resultt::CONSISTENT:
        return resultt::D_SATISFIABLE;
      case refinement_resultt::REFINED:
        continue; // do another iteration
      case refinement_resultt::ERROR:
        return resultt::D_ERROR;
      }
      UNREACHABLE;

    case propt::resultt::P_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;
    case propt::resultt::P_ERROR:
      return resultt::D_ERROR;
    }

    UNREACHABLE;
  }
}

#include <iostream>

bool refinement_solver2t::universal(const quantifiert &quantifier) const
{
  return quantifier.expr.id() == ID_exists ? prop.l_get(quantifier.l).is_false()
         : quantifier.expr.id() == ID_forall
           ? prop.l_get(quantifier.l).is_true()
           : false;
}

bool refinement_solver2t::existential(const quantifiert &quantifier) const
{
  return quantifier.expr.id() == ID_exists ? prop.l_get(quantifier.l).is_true()
         : quantifier.expr.id() == ID_forall
           ? prop.l_get(quantifier.l).is_false()
           : false;
}

refinement_solver2t::refinement_resultt refinement_solver2t::model_refinement()
{
  auto result = refinement_resultt::CONSISTENT;

  // quantifiers
  for(auto &q : quantifier_list)
  {
    switch(refine_quantifier(q))
    {
    case refinement_resultt::CONSISTENT:
      break;

    case refinement_resultt::REFINED:
      result = refinement_resultt::REFINED;
      break;

    case refinement_resultt::ERROR:
      return refinement_resultt::ERROR;
    }
  }

  return result;
}

refinement_solver2t::refinement_resultt
refinement_solver2t::refine_quantifier(const quantifiert &quantifier)
{
  if(universal(quantifier))
  {
    // To contradict the quantifier, try to find a model that
    // satisfies the existential, or that refutes the universal.
    std::cout << "Qu " << prop.l_get(quantifier.l) << ": "
              << format(quantifier.expr) << "\n";
    auto l_where = convert(quantifier.expr.where());

    if(quantifier.expr.id() == ID_exists)
      prop.set_assumptions({l_where});
    else // forall
      prop.set_assumptions({!l_where});

    if(prop.prop_solve() == propt::resultt::P_SATISFIABLE)
    {
      if(quantifier.expr.id() == ID_exists)
        prop.l_set_to_true(quantifier.l);
      else // forall
        prop.l_set_to_false(quantifier.l);

      prop.set_assumptions({});
      return refinement_resultt::REFINED;
    }

    prop.set_assumptions({});
  }
  else if(existential(quantifier))
  {
    // To contradict the quantifier, try to
    // refute the existential, or prove the universal.
    std::cout << "Qe " << prop.l_get(quantifier.l) << ": "
              << format(quantifier.expr) << "\n";
  }

  return refinement_resultt::CONSISTENT;
}
