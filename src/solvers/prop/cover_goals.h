/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_PROP_COVER_GOALS_H
#define CPROVER_SOLVERS_PROP_COVER_GOALS_H

#include <util/message.h>
#include <util/time_stopping.h>

#include "prop_conv.h"

/*******************************************************************\

   Class: cover_gooalst

 Purpose: Try to cover some given set of goals incrementally.
          This can be seen as a heuristic variant of
          SAT-based set-cover. No minimality guarantee.

\*******************************************************************/

class cover_goalst:public messaget
{
public:
  explicit cover_goalst(prop_convt &_prop_conv):
    prop_conv(_prop_conv)
  {
    start_time=current_time();
  }

  virtual ~cover_goalst();

  // returns result of last run on success
  decision_proceduret::resultt operator()();

  // the goals

  struct goalt
  {
    literalt condition;
    time_periodt seconds;
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

  inline void print_goals_stats(std::ostream &out)
  {
    out << '\n';
    out <<"**#START" << '\n';
    out << "block-id,hit-count,time(s)" << '\n';
    for(std::list<goalt>::const_iterator
        g_it=goals.begin();
        g_it!=goals.end();
        g_it++)
    {
        if(g_it->status == goalt::statust::COVERED)
        {
          out << "0,0," << g_it->seconds << '\n';
        }
    }
    out <<"#END" << '\n';
  }

protected:
  absolute_timet start_time;
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
