/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/threeval.h>

#include "prop.h"
#include "cover_goals.h"

/*******************************************************************\

Function: cover_goalst::mark

  Inputs:

 Outputs:

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

  Inputs:

 Outputs:

 Purpose: Build clause

\*******************************************************************/

void cover_goalst::constraint()
{
  bvt bv;

  for(std::list<cover_goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered && !g_it->condition.is_false())
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
      mark(); // mark the ones we got
      break;

    default:
      error("decision procedure failed");
      return;
    }
  }
  while(dec_result==decision_proceduret::D_SATISFIABLE &&
        number_covered()<size());
}

