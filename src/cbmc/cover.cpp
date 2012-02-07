/*******************************************************************\

Module: Vacuity Checks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/sat/satcheck_minisat2.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

   Class: cover_gooalst

 Purpose: Try to cover some given set of goals

\*******************************************************************/

class cover_goalst:public messaget
{
public:
  explicit inline cover_goalst(prop_convt &_prop_conv):
    prop_conv(_prop_conv), prop(_prop_conv.prop)
  {
  }

  void operator()();

  // statistics

  inline unsigned number_covered() const
  {
    return _number_covered;
  }
  
  inline unsigned iterations() const
  {
    return _iterations;
  }
  
  inline unsigned size() const
  {
    return goals.size();
  }
  
  // managing the goals

  inline void add(const literalt condition, const std::string &description)
  {
    goals.push_back(cover_goalt());
    goals.back().condition=condition;
    goals.back().description=description;    
  }
  
  struct cover_goalt
  {
    literalt condition;
    bool covered;
    std::string description;
    
    cover_goalt():covered(false)
    {
    }
  };

  std::list<cover_goalt> goals;

protected:
  unsigned _number_covered, _iterations;
  prop_convt &prop_conv;
  propt &prop;

  void mark();
  void constraint();
};

/*******************************************************************\

Function: cover_goalst::operator()

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

void cover_goalst::mark()
{
  for(std::list<cover_goalt>::iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered &&
       prop.l_get(g_it->condition).is_true())
    {
      g_it->covered=true;
      _number_covered++;
    }
}
  
/*******************************************************************\

Function: cover_goalst::constaint

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

void cover_goalst::constraint()
{
  bvt bv;

  for(std::list<cover_goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered)
      bv.push_back(g_it->condition);

  prop.lcnf(bv);
}

/*******************************************************************\

Function: cover_goalst::operator()

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

void cover_goalst::operator()()
{
  _iterations=_number_covered=0;
  decision_proceduret::resultt dec_result;

  status("Total number of coverage goals: "+i2string(size()));

  do
  {
    // We want (at least) one of the remaining goals, please!
    _iterations++;
    constraint();
    dec_result=prop_conv.dec_solve();
    
    switch(dec_result)
    {
    case decision_proceduret::D_UNSATISFIABLE: // DONE
      break;

    case decision_proceduret::D_SATISFIABLE: // more assertions
      // mark the ones we got
      mark();
      break;

    default:
      error("decision procedure failed");
      return;
    }
  }
  while(dec_result==decision_proceduret::D_SATISFIABLE &&
        number_covered()<size());
}

/*******************************************************************\

Function: bmct::cover_assertions

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

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

  // collect goals in `goal_map'
  literalt assumption_literal=const_literal(true);
  
  typedef std::map<goto_programt::const_targett, bvt> goal_mapt;
  goal_mapt goal_map;

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

      goal_map[it->source.pc].push_back(l);
    }
    else if(it->is_assume())
      assumption_literal=
        prop_conv.prop.land(assumption_literal, it->cond_literal);
  
  // compute
  cover_goalst cover_goals(prop_conv);
  cover_goals.set_message_handler(get_message_handler());
  cover_goals.set_verbosity(get_verbosity());

  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    literalt condition=prop_conv.prop.lor(it->second);
    cover_goals.add(condition, it->first->location.as_string());
  }

  cover_goals();

  // report
  for(std::list<cover_goalst::cover_goalt>::const_iterator
      g_it=cover_goals.goals.begin();
      g_it!=cover_goals.goals.end();
      g_it++)
    if(!g_it->covered)
    {
      warning("!! failed to cover "+g_it->description);
    }

  status("");
  status("** Covered "+i2string(cover_goals.number_covered())+
         " of "+i2string(cover_goals.size())+" in "+
         i2string(cover_goals.iterations())+" iterations");
}
