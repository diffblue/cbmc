/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Cover a set of goals incrementally

#ifndef CPROVER_SOLVERS_PROP_COVER_GOALS_H
#define CPROVER_SOLVERS_PROP_COVER_GOALS_H

#include <list>

#include <solvers/decision_procedure.h>

#include <util/expr.h>

class message_handlert;

/// Try to cover some given set of goals incrementally. This can be seen as a
/// heuristic variant of SAT-based set-cover. No minimality guarantee.
class cover_goalst
{
public:
  explicit cover_goalst(decision_proceduret &_decision_procedure)
    : _number_covered(0),
      _iterations(0),
      decision_procedure(_decision_procedure)
  {
  }

  virtual ~cover_goalst();

  // returns result of last run on success
  decision_proceduret::resultt operator()(message_handlert &);

  // the goals

  struct goalt
  {
    exprt condition;
    enum class statust { UNKNOWN, COVERED, UNCOVERED, ERROR } status;

    explicit goalt(exprt _condition)
      : condition(std::move(_condition)), status(statust::UNKNOWN)
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

  void add(exprt condition)
  {
    goals.emplace_back(std::move(condition));
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
  decision_proceduret &decision_procedure;

  typedef std::vector<observert *> observerst;
  observerst observers;

private:
  void mark();
  void constraint();
};

#endif // CPROVER_SOLVERS_PROP_COVER_GOALS_H
