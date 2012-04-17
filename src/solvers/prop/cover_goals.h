/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_COVER_GOALS_H
#define CPROCER_COVER_GOALS_H

#include <message.h>

#include "prop_conv.h"

/*******************************************************************\

   Class: cover_gooalst

 Purpose: Try to cover some given set of goals

\*******************************************************************/

class cover_goalst:public messaget
{
public:
  explicit inline cover_goalst(prop_convt &_prop_conv):
    prop_conv(_prop_conv), prop(_prop_conv.prop)
  {
  }

  void operator()();

  // statistics

  inline unsigned number_covered() const
  {
    return _number_covered;
  }
  
  inline unsigned iterations() const
  {
    return _iterations;
  }
  
  inline unsigned size() const
  {
    return goals.size();
  }
  
  // managing the goals

  inline void add(
    const literalt condition,
    const std::string &description)
  {
    goals.push_back(cover_goalt());
    goals.back().condition=condition;
    goals.back().description=description;    
  }
  
  struct cover_goalt
  {
    literalt condition;
    bool covered;
    std::string description;
    
    cover_goalt():covered(false)
    {
    }
  };

  std::list<cover_goalt> goals;

protected:
  unsigned _number_covered, _iterations;
  prop_convt &prop_conv;
  propt &prop;

  void mark();
  void constraint();
};

#endif
