/*******************************************************************\

Module: Vacuity Checks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/sat/satcheck_minisat2.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

Function: bmct::cover_assertions

  Inputs:

 Outputs:

 Purpose: Try to reach all assertions

\*******************************************************************/

class cover_goalst
{
public:
  struct cover_goalt
  {
    literalt l;
    goto_programt::const_targett pc;
    bool covered;
    
    cover_goalt():covered(false)
    {
    }
  };

  std::list<cover_goalt> goals;
  unsigned number_covered;
  
  cover_goalst():number_covered(0)
  {
  }

  void mark(const propt &prop)
  {
    for(std::list<cover_goalt>::const_iterator
        g_it=goals.begin();
        g_it!=goals.end();
        g_it++)
      if(!g_it->covered &&
         prop.l_get(g_it->l).is_true())
      {
        // mark all goals with the same location
        for(std::list<cover_goalt>::iterator
            g_it2=goals.begin();
            g_it2!=goals.end();
            g_it2++)
          if(g_it2->pc==g_it->pc)
          {
            g_it2->covered=true;
            number_covered++;
          }
      }
  }
  
  void constraint(propt &dest)
  {
    bvt bv;
  
    for(std::list<cover_goalt>::const_iterator
        g_it=goals.begin();
        g_it!=goals.end();
        g_it++)
      if(!g_it->covered)
        bv.push_back(g_it->l);

    dest.lcnf(bv);
  }

  void add(const literalt l, goto_programt::const_targett pc)
  {
    goals.push_back(cover_goalt());
    goals.back().l=l;
    goals.back().pc=pc;
  }
};

void bmct::cover_assertions()
{
  // with simplifier: need to freeze goal variables
  // to prevent them from being eliminated
  satcheck_minisat_no_simplifiert satcheck;
  
  satcheck.set_message_handler(get_message_handler());
  satcheck.set_verbosity(get_verbosity());
  
  bv_cbmct bv_cbmc(ns, satcheck);
  bv_cbmc.set_message_handler(get_message_handler());
  bv_cbmc.set_verbosity(get_verbosity());
  
  if(options.get_option("arrays-uf")=="never")
    bv_cbmc.unbounded_array=bv_cbmct::U_NONE;
  else if(options.get_option("arrays-uf")=="always")
    bv_cbmc.unbounded_array=bv_cbmct::U_ALL;

  prop_convt &prop_conv=bv_cbmc;

  // convert

  equation.convert_guards(prop_conv);
  equation.convert_assignments(prop_conv);
  equation.convert_decls(prop_conv);
  equation.convert_assumptions(prop_conv);

  // collect goals
  
  literalt assumption_literal=const_literal(true);
  cover_goalst cover_goals;

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
    if(it->is_assert())
    {
      // we just want reachability, i.e., the guard,
      // not the assertion itself
      literalt l=
        prop_conv.prop.land(assumption_literal, it->guard_literal);

      cover_goals.add(l, it->source.pc);
    }
    else if(it->is_assume())
      assumption_literal=
        prop_conv.prop.land(assumption_literal, it->cond_literal);
  
  decision_proceduret::resultt dec_result;

  status("Total number of coverage goals: "+i2string(cover_goals.goals.size()));
  
  unsigned iterations=0;

  do
  {
    // We want one of the remaining assertions, please!
    iterations++;
    cover_goals.constraint(prop_conv.prop);
    dec_result=prop_conv.dec_solve();
    
    switch(dec_result)
    {
    case decision_proceduret::D_UNSATISFIABLE: // DONE
      break;

    case decision_proceduret::D_SATISFIABLE: // more assertions
      // mark the ones we got
      cover_goals.mark(prop_conv.prop);
      break;

    default:
      error("decision procedure failed");
      return;
    }
  }
  while(dec_result==decision_proceduret::D_SATISFIABLE &&
        cover_goals.number_covered<cover_goals.goals.size());
  
  for(std::list<cover_goalst::cover_goalt>::const_iterator
      g_it=cover_goals.goals.begin();
      g_it!=cover_goals.goals.end();
      g_it++)
    if(!g_it->covered)
    {
      warning("!! failed to cover "+g_it->pc->location.as_string());
    }

  status("");
  status("** Covered "+i2string(cover_goals.number_covered)+
         " in "+i2string(iterations)+" iterations");
}
