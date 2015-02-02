/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_COVER_GOALS_H
#define CPROVER_COVER_GOALS_H

#include <util/message.h>

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
  explicit inline cover_goalst(prop_convt &_prop_conv):
    prop_conv(_prop_conv)
  {
  }
  
  virtual ~cover_goalst();

  void operator()();

  // the goals

  struct goalt
  {
    literalt condition;
    bool covered;
    
    goalt():covered(false)
    {
    }
  };

  typedef std::list<goalt> goalst;
  goalst goals;
  
  // statistics

  inline unsigned number_covered() const
  {
    return _number_covered;
  }
  
  inline unsigned iterations() const
  {
    return _iterations;
  }
  
  inline goalst::size_type size() const
  {
    return goals.size();
  }
  
  // managing the goals

  inline void add(const literalt condition)
  {
    goals.push_back(goalt());
    goals.back().condition=condition;
  }
  
  // register an observer if you want to be told
  // about satisfying assignments
  
  class observert
  {
  public:
    virtual void goal_covered(const goalt &)=0;
  };
  
  inline void register_observer(observert &o)
  {
    observers.push_back(&o);
  }
  
protected:
  unsigned _number_covered, _iterations;
  prop_convt &prop_conv;

  typedef std::vector<observert *> observerst;
  observerst observers;

private:
  void mark();
  void constraint();
  void freeze_goal_variables();
};

#endif
