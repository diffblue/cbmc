/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_refinement.h"

#include <util/xml.h>

bv_refinementt::bv_refinementt(const infot &info):
  bv_pointerst(*info.ns, *info.prop),
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
  status() << "BV-Refinement: post-processing" << eom;
  post_process();

  debug() << "Solving with " << prop.solver_text() << eom;

  unsigned iteration=0;

  // now enter the loop
  while(true)
  {
    iteration++;

    status() << "BV-Refinement: iteration " << iteration << eom;

    // output the very same information in a structured fashion
    if(config_.output_xml)
    {
      xmlt xml("refinement-iteration");
      xml.data=std::to_string(iteration);
      status() << xml << '\n';
    }

    switch(prop_solve())
    {
    case resultt::D_SATISFIABLE:
      check_SAT();
      if(!progress)
      {
        status() << "BV-Refinement: got SAT, and it simulates => SAT" << eom;
        status() << "Total iterations: " << iteration << eom;
        return resultt::D_SATISFIABLE;
      }
      else
        status() << "BV-Refinement: got SAT, and it is spurious, refining"
                 << eom;
      break;

    case resultt::D_UNSATISFIABLE:
      check_UNSAT();
      if(!progress)
      {
        status() << "BV-Refinement: got UNSAT, and the proof passes => UNSAT"
                 << eom;
        status() << "Total iterations: " << iteration << eom;
        return resultt::D_UNSATISFIABLE;
      }
      else
        status() << "BV-Refinement: got UNSAT, and the proof fails, refining"
                 << eom;
      break;

    default:
      return resultt::D_ERROR;
    }
  }
}

decision_proceduret::resultt bv_refinementt::prop_solve()
{
  // this puts the underapproximations into effect
  bvt assumptions=parent_assumptions;

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

  prop.set_assumptions(assumptions);
  propt::resultt result=prop.prop_solve();
  prop.set_assumptions(parent_assumptions);

  switch(result)
  {
    case propt::resultt::P_SATISFIABLE: return resultt::D_SATISFIABLE;
    case propt::resultt::P_UNSATISFIABLE: return resultt::D_UNSATISFIABLE;
    default: return resultt::D_ERROR;
  }

  UNREACHABLE;
}

void bv_refinementt::check_SAT()
{
  progress=false;

  arrays_overapproximated();

  for(approximationt &approximation : this->approximations)
    check_SAT(approximation);
}

void bv_refinementt::check_UNSAT()
{
  progress=false;

  for(approximationt &approximation : this->approximations)
    check_UNSAT(approximation);
}

void bv_refinementt::set_assumptions(const bvt &_assumptions)
{
  parent_assumptions=_assumptions;
  prop.set_assumptions(_assumptions);
}
