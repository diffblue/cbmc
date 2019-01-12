/*******************************************************************\

Module: Minimize some target function incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Minimize some target function incrementally

#include "minimize.h"

#include <util/threeval.h>

#include "literal_expr.h"

/// Add an objective
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

/// Fix objectives that are satisfied
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

  POSTCONDITION(found);
}

/// Build constraints that require us to improve on at least one goal, greedily.
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
    exprt::operandst disjuncts;
    disjuncts.reserve(or_clause.size());
    forall_literals(it, or_clause)
      disjuncts.push_back(literal_exprt(*it));

    return prop_conv.convert(disjunction(disjuncts));
  }
}

/// Try to cover all objectives
void prop_minimizet::operator()()
{
  // we need to use assumptions
  PRECONDITION(prop_conv.has_set_assumptions());

  _iterations=0;
  _number_satisfied=0;
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
        dec_result=decision_proceduret::resultt::D_UNSATISFIABLE;
      else
      {
        _iterations++;

        bvt assumptions;
        assumptions.push_back(c);
        prop_conv.set_assumptions(assumptions);
        dec_result=prop_conv.dec_solve();

        switch(dec_result)
        {
        case decision_proceduret::resultt::D_UNSATISFIABLE:
          last_was_SAT=false;
          break;

        case decision_proceduret::resultt::D_SATISFIABLE:
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
    while(dec_result!=decision_proceduret::resultt::D_UNSATISFIABLE);
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
