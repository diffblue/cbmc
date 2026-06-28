/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_refinement.h"

#include <util/xml.h>

template <typename bv_pointers_baset>
bv_refinementt<bv_pointers_baset>::bv_refinementt(const infot &info)
  : bv_pointers_baset(*info.ns, *info.prop, *info.message_handler),
    progress(false),
    config_(info)
{
  // check features we need
  PRECONDITION(this->prop.has_assumptions());
  PRECONDITION(this->prop.has_set_to());
  PRECONDITION(this->prop.has_is_in_conflict());
}

template <typename bv_pointers_baset>
decision_proceduret::resultt
bv_refinementt<bv_pointers_baset>::dec_solve(const exprt &assumption)
{
  // do the usual post-processing
  this->log.progress() << "BV-Refinement: post-processing" << messaget::eom;
  this->finish_eager_conversion();

  this->log.debug() << "Solving with " << this->prop.solver_text()
                    << messaget::eom;

  unsigned iteration=0;

  // now enter the loop
  while(true)
  {
    iteration++;

    this->log.progress() << "BV-Refinement: iteration " << iteration
                         << messaget::eom;

    // output the very same information in a structured fashion
    if(config_.output_xml)
    {
      xmlt xml("refinement-iteration");
      xml.data=std::to_string(iteration);
      this->log.status() << xml << '\n';
    }

    switch(prop_solve())
    {
    case resultt::D_SATISFIABLE:
      check_SAT();
      if(!progress)
      {
        this->log.status() << "BV-Refinement: got SAT, and it simulates => SAT"
                           << messaget::eom;
        this->log.statistics()
          << "Total iterations: " << iteration << messaget::eom;
        return resultt::D_SATISFIABLE;
      }
      else
        this->log.progress()
          << "BV-Refinement: got SAT, and it is spurious, refining"
          << messaget::eom;
      break;

    case resultt::D_UNSATISFIABLE:
      check_UNSAT();
      if(!progress)
      {
        this->log.status()
          << "BV-Refinement: got UNSAT, and the proof passes => UNSAT"
          << messaget::eom;
        this->log.statistics()
          << "Total iterations: " << iteration << messaget::eom;
        return resultt::D_UNSATISFIABLE;
      }
      else
        this->log.progress()
          << "BV-Refinement: got UNSAT, and the proof fails, refining"
          << messaget::eom;
      break;

    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}

template <typename bv_pointers_baset>
decision_proceduret::resultt bv_refinementt<bv_pointers_baset>::prop_solve()
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

  this->push(assumptions);
  propt::resultt result = this->prop.prop_solve(this->assumption_stack);
  this->pop();

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

template <typename bv_pointers_baset>
void bv_refinementt<bv_pointers_baset>::check_SAT()
{
  progress=false;

  arrays_overapproximated();

  // get values before modifying the formula
  for(approximationt &approximation : this->approximations)
    get_values(approximation);

  for(approximationt &approximation : this->approximations)
    check_SAT(approximation);
}

template <typename bv_pointers_baset>
void bv_refinementt<bv_pointers_baset>::check_UNSAT()
{
  progress=false;

  for(approximationt &approximation : this->approximations)
    check_UNSAT(approximation);
}

// Explicit instantiations
#include <solvers/flattening/bv_pointers_wide.h>

template class bv_refinementt<bv_pointerst>;
template class bv_refinementt<bv_pointers_widet>;
