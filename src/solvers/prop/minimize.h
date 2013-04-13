/*******************************************************************\

Module: Cover a set of objectives incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_MINIMIZE_H
#define CPROVER_PROP_MINIMIZE_H

#include <map>

#include <util/message.h>

#include "prop_conv.h"

/*******************************************************************\

   Class: prop_minimizet

 Purpose: Try to cover some given set of objectives

\*******************************************************************/

class prop_minimizet:public messaget
{
public:
  explicit inline prop_minimizet(prop_convt &_prop_conv):
    _number_objectives(0),
    prop_conv(_prop_conv),
    prop(_prop_conv.prop)
  {
  }

  void operator()();

  // statistics

  inline unsigned number_satisfied() const
  {
    return _number_satisfied;
  }
  
  inline unsigned iterations() const
  {
    return _iterations;
  }
  
  inline unsigned size() const
  {
    return _number_objectives;
  }
  
  // managing the objectives
  
  typedef long long signed int weightt;

  void objective(
    const literalt condition,
    const weightt weight=1);

  struct objectivet
  {
    literalt condition;
    bool fixed;
    
    explicit objectivet(const literalt _condition):
      condition(_condition), fixed(false)
    {
    }
  };

  typedef std::map<weightt, std::vector<objectivet> > objectivest;
  objectivest objectives;

protected:
  unsigned _iterations, _number_satisfied, _number_objectives;
  weightt _value;
  prop_convt &prop_conv;
  propt &prop;

  literalt constraint();
  void block();
  
  std::vector<bool> assignment;
  void save_assignment();
  void restore_assignment();
  
  objectivest::reverse_iterator current;
};

#endif
