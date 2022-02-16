/*******************************************************************\

Module: Uninterpreted Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Uninterpreted Functions

#ifndef CPROVER_SOLVERS_LOWERING_FUNCTIONS_H
#define CPROVER_SOLVERS_LOWERING_FUNCTIONS_H

#include <map>
#include <set>

#include <util/mathematical_expr.h>

class decision_proceduret;

class functionst
{
public:
  explicit functionst(decision_proceduret &_decision_procedure)
    : decision_procedure(_decision_procedure)
  {
  }

  virtual ~functionst()
  {
  }

  void record(const function_application_exprt &function_application);

  virtual void finish_eager_conversion()
  {
    add_function_constraints();
  }

protected:
  decision_proceduret &decision_procedure;

  typedef std::set<function_application_exprt> applicationst;

  struct function_infot
  {
    applicationst applications;
  };

  typedef std::map<exprt, function_infot> function_mapt;
  function_mapt function_map;

  virtual void add_function_constraints();
  virtual void add_function_constraints(const function_infot &info);

  exprt arguments_equal(const exprt::operandst &o1, const exprt::operandst &o2);
};

#endif // CPROVER_SOLVERS_LOWERING_FUNCTIONS_H
