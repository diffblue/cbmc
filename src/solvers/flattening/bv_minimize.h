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

class bv_minimizet
{
public:
  bv_minimizet(boolbvt &_boolbv, message_handlert &message_handler)
    : boolbv(_boolbv), log(message_handler)
  {
  }

  void operator()(const minimization_listt &objectives);

protected:
  boolbvt &boolbv;
  messaget log;

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

  bv_minimizing_dect(const namespacet &_ns, message_handlert &message_handler)
    : bv_pointerst(_ns, satcheck, message_handler),
      satcheck(message_handler),
      log(message_handler)
  {
  }

  void minimize(const minimization_listt &objectives)
  {
    bv_minimizet bv_minimize{*this, log.get_message_handler()};
    bv_minimize(objectives);
  }

  satcheckt satcheck;
  messaget log;
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_MINIMIZE_H
