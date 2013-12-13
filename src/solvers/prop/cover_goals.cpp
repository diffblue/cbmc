/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/threeval.h>

#include "prop.h"
#include "cover_goals.h"

/*******************************************************************\

Function: cover_goalst::~cover_goalst

  Inputs: -

 Outputs: -

 Purpose: constructor

\*******************************************************************/

cover_goalst::~cover_goalst()
{
}

/*******************************************************************\

Function: cover_goalst::mark

  Inputs: -

 Outputs: -

 Purpose: Mark goals that are covered

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

  Inputs: -

 Outputs: -

 Purpose: Build clause (activation literal, non-covered assertion 1 ... 
                                            non-covered assertion n)
          and add it to the solver's database

\*******************************************************************/

void cover_goalst::constraint()
{
  bvt bv;

  bv.push_back(activation_literal);
   
  for(std::list<cover_goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered && !g_it->condition.is_false())
      bv.push_back(g_it->condition);

#if 0
  std::cout << "cover_goals.assertion_clause = ";
  forall_literals(it, bv) 
    std::cout << *it << ", ";
  std::cout << std::endl;
#endif

  prop.lcnf(bv);
}

/*******************************************************************\

Function: cover_goalst::freeze_goal_variables

  Inputs:

 Outputs:

 Purpose: Build clause

\*******************************************************************/

void cover_goalst::freeze_goal_variables()
{
  for(std::list<cover_goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->condition.is_constant())
      prop.set_frozen(g_it->condition);
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
  
  #if 1
  propt::resultt prop_result;
  
  // We use incremental solving, so need to freeze some variables
  // to prevent them from being eliminated.      
  freeze_goal_variables();

  // Do post-processing in decision procedure, just once
  prop_conv.post_process();

  do
  {
    // We want (at least) one of the remaining goals, please!
    _iterations++;
    
    constraint();
    prop_result=prop.prop_solve();
    
    switch(prop_result)
    {
    case propt::P_UNSATISFIABLE: // DONE
      break;

    case propt::P_SATISFIABLE:
      // mark the goals we got
      mark(); 
      
      // notify
      assignment();
      break;

    default:
      error("propositional solver has failed");
      return;
    }
  }
  while(prop_result==propt::P_SATISFIABLE &&
        number_covered()<size());
  #else
  decision_proceduret::resultt dec_result;
  
  // We use incremental solving, so need to freeze some variables
  // to prevent them from being eliminated.      
  freeze_goal_variables();

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

    case decision_proceduret::D_SATISFIABLE:
      // mark the goals we got
      mark(); 
      
      // notify
      assignment();
      break;

    default:
      error("decision procedure failed");
      return;
    }
  }
  while(dec_result==decision_proceduret::D_SATISFIABLE &&
        number_covered()<size());
  #endif
}

