/*******************************************************************\

Module: SAT-optimizer for minimizing expressions

Author: Georg Weissenbacher
    
Date: July 2006

Purpose: Find a satisfying assignment that minimizes a given set
         of symbols

\*******************************************************************/

#ifndef CPROVER_BV_MINIMIZER_H
#define CPROVER_BV_MINIMIZER_H

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

typedef std::set<exprt> minimization_listt;

class bv_minimizet:public messaget
{
public:
  explicit bv_minimizet(boolbvt &_boolbv):
    absolute_value(false),
    boolbv(_boolbv)
  {
  }
  
  void operator()(const minimization_listt &objectives);
  
  bool absolute_value;

protected:
  boolbvt &boolbv;
  
  void add_objective(
    class prop_minimizet &prop_minimize,
    const exprt &objective);
};

class bv_minimizing_dect:public bv_pointerst
{
public:
  virtual const std::string description()
  { 
    return "Bit vector minimizing SAT";
  }

  explicit bv_minimizing_dect(const namespacet &_ns):
    bv_pointerst(_ns, satcheck)
  {
  }

  void minimize(const minimization_listt &objectives)
  {
    bv_minimizet bv_minimize(*this);
    bv_minimize.set_message_handler(get_message_handler());
    bv_minimize(objectives);
  }

  satcheckt satcheck;
};

#endif
