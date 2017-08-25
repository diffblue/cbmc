/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Cover a set of goals incrementally

#ifndef CPROVER_SOLVERS_PROP_COVER_GOALS_H
#define CPROVER_SOLVERS_PROP_COVER_GOALS_H

#include <util/message.h>

#include "prop_conv.h"

/// Try to cover some given set of goals incrementally. This can be seen as a
/// heuristic variant of SAT-based set-cover. No minimality guarantee.
class cover_goalst:public messaget
{
public:
  explicit cover_goalst(prop_convt &_prop_conv):
    _number_covered(0),
    _iterations(0),
    prop_conv(_prop_conv)
  {
  }

  virtual ~cover_goalst();

  // returns result of last run on success
  decision_proceduret::resultt operator()();

  // the goals

  struct goalt
  {
    literalt condition;
    enum class statust { UNKNOWN, COVERED, UNCOVERED, ERROR } status;

    goalt():status(statust::UNKNOWN)
    {
    }
  };

  typedef std::list<goalt> goalst;
  goalst goals;

  // statistics

  std::size_t number_covered() const
  {
    return _number_covered;
  }

  unsigned iterations() const
  {
    return _iterations;
  }

  goalst::size_type size() const
  {
    return goals.size();
  }

  // managing the goals

  void add(const literalt condition)
  {
    goals.push_back(goalt());
    goals.back().condition=condition;
  }

  // register an observer if you want to be told
  // about satisfying assignments

  class observert
  {
  public:
    virtual void goal_covered(const goalt &) { }
    virtual void satisfying_assignment() { }
  };

  void register_observer(observert &o)
  {
    observers.push_back(&o);
  }

protected:
  std::size_t _number_covered;
  unsigned _iterations;
  prop_convt &prop_conv;

  typedef std::vector<observert *> observerst;
  observerst observers;

private:
  void mark();
  void constraint();
  void freeze_goal_variables();
};

#endif // CPROVER_SOLVERS_PROP_COVER_GOALS_H
