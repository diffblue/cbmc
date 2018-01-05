/*******************************************************************\

Module: SAT-optimizer for minimizing expressions

Author: Georg Weissenbacher

Date: July 2006

Purpose: Find a satisfying assignment that minimizes a given set
         of symbols

\*******************************************************************/

/// \file
/// SAT-optimizer for minimizing expressions

#ifndef CPROVER_SOLVERS_FLATTENING_BV_MINIMIZE_H
#define CPROVER_SOLVERS_FLATTENING_BV_MINIMIZE_H

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

typedef std::set<exprt> minimization_listt;

class bv_minimizet:public messaget
{
public:
  explicit bv_minimizet(boolbvt &_boolbv):
    boolbv(_boolbv)
  {
  }

  void operator()(const minimization_listt &objectives);

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

  bv_minimizing_dect(const namespacet &_ns, const satcheck_infot &satcheck_info)
    : bv_pointerst(_ns, satcheck)
  {
    satcheck.set_random_var_freq(satcheck_info.random_var_freq);
    satcheck.set_random_seed(satcheck_info.random_seed);
  }

  void minimize(const minimization_listt &objectives)
  {
    bv_minimizet bv_minimize(*this);
    bv_minimize.set_message_handler(get_message_handler());
    bv_minimize(objectives);
  }

  satcheckt satcheck;
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_MINIMIZE_H
