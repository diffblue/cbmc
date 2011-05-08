/*******************************************************************\

Module: SAT-optimizer for minimizing expressions

Author: Georg Weissenbacher
    
Date: July 2006

Purpose: Find a satisfying assignment that minimizes a given set
         of symbols

\*******************************************************************/

#ifndef CPROVER_CEGAR_SAT_OPTIMIZER_H
#define CPROVER_CEGAR_SAT_OPTIMIZER_H

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

typedef std::set<exprt> minimization_listt;

typedef satcheckt sat_minimizert;

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

  bool minimize(const minimization_listt &symbols);

  sat_minimizert satcheck;
};

#endif
