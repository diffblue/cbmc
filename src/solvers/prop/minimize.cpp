/*******************************************************************\

Module: Minimize some target function incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <threeval.h>
#include <i2string.h>

#include "prop.h"
#include "minimize.h"

/*******************************************************************\

Function: prop_minimizet::objective

  Inputs:

 Outputs:

 Purpose: Add an objective

\*******************************************************************/

void prop_minimizet::objective(
  const literalt condition,
  const weightt weight)
{
  if(weight>0)
  {
    objectives[weight].conditions.push_back(condition);
  }
  else if(weight<0)
  {
    objectives[-weight].conditions.push_back(prop.lnot(condition));
  }
}

/*******************************************************************\

Function: prop_minimizet::block

  Inputs:

 Outputs:

 Purpose: Block objectives that are satisfied

\*******************************************************************/

void prop_minimizet::block()
{
  entryt &entry=current->second;
  bool found=false;
  
  for(bvt::iterator
      c_it=entry.conditions.begin();
      c_it!=entry.conditions.end();
      ++c_it)
  {
    if(prop.l_get(*c_it).is_false())
    {
      _number_satisfied++;
      _value+=current->first;
      prop.l_set_to(*c_it, false); // fix it
      found=true;
    }
  }
  
  assert(found);
}
  
/*******************************************************************\

Function: prop_minimizet::constaint

  Inputs:

 Outputs:

 Purpose: Build constraints that require us to improve on
          at least one goal, greedily.

\*******************************************************************/

void prop_minimizet::constraint()
{
  bvt or_clause;
  entryt &entry=current->second;
  
  bvt assumptions;
  assumptions.push_back(prop.lnot(prop.land(entry.conditions)));
  prop.set_assumptions(assumptions);
}

/*******************************************************************\

Function: prop_minimizet::operator()

  Inputs:

 Outputs:

 Purpose: Try to cover all objectives

\*******************************************************************/

void prop_minimizet::operator()()
{
  // we need to use assumptions
  assert(prop_conv.prop.has_set_assumptions());

  _iterations=_number_satisfied=0;
  _value=0;
  decision_proceduret::resultt dec_result;
  
  save_assignment();

  // go from high weights to low ones
  for(current=objectives.rbegin();
      current!=objectives.rend();
      current++)
  {
    status("weight "+i2string(current->first));
  
    // We want to improve on one of the objectives, please!
    _iterations++;
    constraint();
    dec_result=prop_conv.dec_solve();
    
    switch(dec_result)
    {
    case decision_proceduret::D_UNSATISFIABLE:
      restore_assignment();
      break;

    case decision_proceduret::D_SATISFIABLE:
      block(); // block the ones we got
      save_assignment();
      break;

    default:
      error("decision procedure failed");
      return;
    }
  }
}

/*******************************************************************\

Function: prop_minimizet::save_assignment

  Inputs:

 Outputs:

 Purpose:   
   
\*******************************************************************/

void prop_minimizet::save_assignment()
{
  assignment.resize(prop.no_variables());

  for(unsigned i=1; i<prop.no_variables(); i++)
    assignment[i]=prop.l_get(literalt(i, false)).is_true();
}  

/*******************************************************************\

Function: prop_minimizet::restore_assignment

  Inputs:

 Outputs:

 Purpose:   
   
\*******************************************************************/

void prop_minimizet::restore_assignment()
{
  assert(assignment.size()<=prop.no_variables());

  for(unsigned i=1; i<prop.no_variables(); i++)
    prop.set_assignment(literalt(i, false), assignment[i]);
}
