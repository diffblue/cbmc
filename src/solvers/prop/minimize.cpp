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
    objectives[weight].push_back(objectivet(condition));
    _number_objectives++;
  }
  else if(weight<0)
  {
    objectives[-weight].push_back(objectivet(prop.lnot(condition)));
    _number_objectives++;
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
  std::vector<objectivet> &entry=current->second;
  bool found=false;
  
  for(std::vector<objectivet>::iterator
      o_it=entry.begin();
      o_it!=entry.end();
      ++o_it)
  {
    if(!o_it->fixed &&
       prop.l_get(o_it->condition).is_false())
    {
      _number_satisfied++;
      _value+=current->first;
      prop.l_set_to(o_it->condition, false); // fix it
      o_it->fixed=true;
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

literalt prop_minimizet::constraint()
{
  std::vector<objectivet> &entry=current->second;
  bvt or_clause;
  
  for(std::vector<objectivet>::iterator
      o_it=entry.begin();
      o_it!=entry.end();
      ++o_it)
  {
    if(!o_it->fixed)
      or_clause.push_back(prop.lnot(o_it->condition));
  }

  // this returns false if the clause is empty
  return prop.lor(or_clause);
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
  
  save_assignment();

  // go from high weights to low ones
  for(current=objectives.rbegin();
      current!=objectives.rend();
      current++)
  {
    status("weight "+i2string(current->first));

    decision_proceduret::resultt dec_result;
    do
    {  
      // We want to improve on one of the objectives, please!
      literalt c=constraint();
    
      if(c.is_false())
        dec_result=decision_proceduret::D_UNSATISFIABLE;
      else
      {
        _iterations++;

        bvt assumptions;
        assumptions.push_back(c);
        prop_conv.prop.set_assumptions(assumptions);
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
    while(dec_result!=decision_proceduret::D_UNSATISFIABLE);
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
