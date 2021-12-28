/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "refinement_solver.h"

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

refinement_solver2t::refinement_resultt refinement_solver2t::model_refinement()
{
  return refinement_resultt::CONSISTENT;
}
