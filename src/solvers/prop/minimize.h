/*******************************************************************\

Module: Cover a set of objectives incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_MINIMIZE_H
#define CPROVER_PROP_MINIMIZE_H

#include <map>

#include <message.h>

#include "prop_conv.h"

/*******************************************************************\

   Class: prop_minimizet

 Purpose: Try to cover some given set of objectives

\*******************************************************************/

class prop_minimizet:public messaget
{
public:
  explicit inline prop_minimizet(prop_convt &_prop_conv):
    prop_conv(_prop_conv), prop(_prop_conv.prop)
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
    return objectives.size();
  }
  
  // managing the objectives
  
  typedef long long signed int weightt;

  void objective(
    const literalt condition,
    const weightt weight=1);
  
  struct entryt
  {
    bvt conditions;
  };

  typedef std::map<weightt, entryt> objectivest;
  objectivest objectives;

protected:
  unsigned _iterations, _number_satisfied;
  weightt _value;
  prop_convt &prop_conv;
  propt &prop;

  void constraint();
  void block();
  
  std::vector<bool> assignment;
  void save_assignment();
  void restore_assignment();
  
  objectivest::reverse_iterator current;
};

#endif
