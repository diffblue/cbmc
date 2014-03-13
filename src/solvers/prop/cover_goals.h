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

  struct cover_goalt
  {
    literalt condition;
    bool covered;
    
    cover_goalt():covered(false)
    {
    }
  };

  typedef std::list<cover_goalt> goalst;
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
    goals.push_back(cover_goalt());
    goals.back().condition=condition;
  }
  
protected:
  unsigned _number_covered, _iterations;
  prop_convt &prop_conv;

  // this method is called for each satisfying assignment
  virtual void assignment()
  {
  }

private:
  void mark();
  void constraint();
  void freeze_goal_variables();
};

#endif
