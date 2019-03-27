/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Cover a set of goals incrementally

#include "cover_goals.h"

#include <util/message.h>
#include <util/threeval.h>

#include "decision_procedure_incremental.h"
#include "literal_expr.h"

cover_goalst::~cover_goalst()
{
}

/// Mark goals that are covered
void cover_goalst::mark()
{
  // notify observers
  for(const auto &o : observers)
    o->satisfying_assignment();

  for(auto &g : goals)
    if(
      g.status == goalt::statust::UNKNOWN &&
      decision_procedure.l_get(g.condition).is_true())
    {
      g.status=goalt::statust::COVERED;
      _number_covered++;

      // notify observers
      for(const auto &o : observers)
        o->goal_covered(g);
    }
}

/// Build clause
void cover_goalst::constraint()
{
  exprt::operandst disjuncts;

  // cover at least one unknown goal

  for(std::list<goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(g_it->status==goalt::statust::UNKNOWN &&
       !g_it->condition.is_false())
      disjuncts.push_back(literal_exprt(g_it->condition));

  // this is 'false' if there are no disjuncts
  decision_procedure.set_to_true(disjunction(disjuncts));
}

/// Build clause
void cover_goalst::freeze_goal_variables()
{
  for(std::list<goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->condition.is_constant())
      decision_procedure.set_frozen(g_it->condition);
}

/// Try to cover all goals
decision_proceduret::resultt cover_goalst::
operator()(message_handlert &message_handler)
{
  _iterations=_number_covered=0;

  decision_proceduret::resultt dec_result;

  // We use incremental solving, so need to freeze some variables
  // to prevent them from being eliminated.
  freeze_goal_variables();

  do
  {
    // We want (at least) one of the remaining goals, please!
    _iterations++;

    constraint();
    dec_result = decision_procedure();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_UNSATISFIABLE: // DONE
      return dec_result;

    case decision_proceduret::resultt::D_SATISFIABLE:
      // mark the goals we got, and notify observers
      mark();
      break;

    default:
    {
      messaget log(message_handler);
      log.error() << "decision procedure has failed" << messaget::eom;
      return dec_result;
    }
    }
  }
  while(dec_result==decision_proceduret::resultt::D_SATISFIABLE &&
        number_covered()<size());

  return decision_proceduret::resultt::D_SATISFIABLE;
}
