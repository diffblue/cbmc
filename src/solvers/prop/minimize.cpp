/*******************************************************************\

Module: Minimize some target function incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/threeval.h>

#include "literal_expr.h"
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
    objectives[-weight].push_back(objectivet(!condition));
    _number_objectives++;
  }
}

/*******************************************************************\

Function: prop_minimizet::fix

  Inputs:

 Outputs:

 Purpose: Fix objectives that are satisfied

\*******************************************************************/

void prop_minimizet::fix_objectives()
{
  std::vector<objectivet> &entry=current->second;
  bool found=false;
  
  for(std::vector<objectivet>::iterator
      o_it=entry.begin();
      o_it!=entry.end();
      ++o_it)
  {
    if(!o_it->fixed &&
       prop_conv.l_get(o_it->condition).is_false())
    {
      _number_satisfied++;
      _value+=current->first;
      prop_conv.set_to(literal_exprt(o_it->condition), false); // fix it
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
      or_clause.push_back(!o_it->condition);
  }

  // This returns false if the clause is empty,
  // i.e., no further improvement possible.
  if(or_clause.empty())
    return const_literal(false);
  else if(or_clause.size()==1)
    return or_clause.front();
  else
  {
    or_exprt or_expr;
    forall_literals(it, or_clause)
      or_expr.copy_to_operands(literal_exprt(*it));
    
    return prop_conv.convert(or_expr);
  }
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
  assert(prop_conv.has_set_assumptions());

  _iterations=_number_satisfied=0;
  _value=0;
  bool last_was_SAT=false;
  
  // go from high weights to low ones
  for(current=objectives.rbegin();
      current!=objectives.rend();
      current++)
  {
    status() << "weight " << current->first << eom;

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
        prop_conv.set_assumptions(assumptions);
        dec_result=prop_conv.dec_solve();
    
        switch(dec_result)
        {
        case decision_proceduret::D_UNSATISFIABLE:
          last_was_SAT=false;
          break;

        case decision_proceduret::D_SATISFIABLE:
          last_was_SAT=true;
          fix_objectives(); // fix the ones we got
          break;

        default:
          error() << "decision procedure failed" << eom;
          last_was_SAT=false;
          return;
        }
      }
    }
    while(dec_result!=decision_proceduret::D_UNSATISFIABLE);
  }
  
  if(!last_was_SAT)
  {
    // We don't have a satisfying assignment to work with.
    // Run solver again to get one.

    bvt assumptions; // no assumptions
    prop_conv.set_assumptions(assumptions);
    prop_conv.dec_solve();
  }
}

