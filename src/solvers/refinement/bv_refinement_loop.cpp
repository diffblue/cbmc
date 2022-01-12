/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_refinement.h"

#include <util/xml.h>

bv_refinementt::bv_refinementt(const infot &info)
  : bv_pointerst(*info.ns, *info.prop, *info.message_handler),
    progress(false),
    config_(info)
{
  // check features we need
  PRECONDITION(prop.has_set_assumptions());
  PRECONDITION(prop.has_set_to());
  PRECONDITION(prop.has_is_in_conflict());
}

decision_proceduret::resultt bv_refinementt::dec_solve()
{
  // do the usual post-processing
  log.status() << "BV-Refinement: post-processing" << messaget::eom;
  finish_eager_conversion();

  log.debug() << "Solving with " << prop.solver_text() << messaget::eom;

  unsigned iteration=0;

  // now enter the loop
  while(true)
  {
    iteration++;

    log.status() << "BV-Refinement: iteration " << iteration << messaget::eom;

    // output the very same information in a structured fashion
    if(config_.output_xml)
    {
      xmlt xml("refinement-iteration");
      xml.data=std::to_string(iteration);
      log.status() << xml << '\n';
    }

    switch(prop_solve())
    {
    case resultt::D_SATISFIABLE:
      check_SAT();
      if(!progress)
      {
        log.status() << "BV-Refinement: got SAT, and it simulates => SAT"
                     << messaget::eom;
        log.status() << "Total iterations: " << iteration << messaget::eom;
        return resultt::D_SATISFIABLE;
      }
      else
        log.status() << "BV-Refinement: got SAT, and it is spurious, refining"
                     << messaget::eom;
      break;

    case resultt::D_UNSATISFIABLE:
      check_UNSAT();
      if(!progress)
      {
        log.status()
          << "BV-Refinement: got UNSAT, and the proof passes => UNSAT"
          << messaget::eom;
        log.status() << "Total iterations: " << iteration << messaget::eom;
        return resultt::D_UNSATISFIABLE;
      }
      else
        log.status()
          << "BV-Refinement: got UNSAT, and the proof fails, refining"
          << messaget::eom;
      break;

    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}

decision_proceduret::resultt bv_refinementt::prop_solve()
{
  // this puts the underapproximations into effect
  std::vector<exprt> assumptions;

  for(const approximationt &approximation : approximations)
  {
    assumptions.insert(
      assumptions.end(),
      approximation.over_assumptions.begin(),
      approximation.over_assumptions.end());
    assumptions.insert(
      assumptions.end(),
      approximation.under_assumptions.begin(),
      approximation.under_assumptions.end());
  }

  push(assumptions);
  propt::resultt result=prop.prop_solve();
  pop();

  // clang-format off
  switch(result)
  {
  case propt::resultt::P_SATISFIABLE: return resultt::D_SATISFIABLE;
  case propt::resultt::P_UNSATISFIABLE: return resultt::D_UNSATISFIABLE;
  case propt::resultt::P_ERROR: return resultt::D_ERROR;
  }
  // clang-format off

  UNREACHABLE;
}

void bv_refinementt::check_SAT()
{
  progress=false;

  arrays_overapproximated();

  // get values before modifying the formula
  for(approximationt &approximation : this->approximations)
    get_values(approximation);

  for(approximationt &approximation : this->approximations)
    check_SAT(approximation);
}

void bv_refinementt::check_UNSAT()
{
  progress=false;

  for(approximationt &approximation : this->approximations)
    check_UNSAT(approximation);
}
