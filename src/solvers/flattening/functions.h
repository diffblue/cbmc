/*******************************************************************\

Module: Uninterpreted Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Uninterpreted Functions

#ifndef CPROVER_SOLVERS_FLATTENING_FUNCTIONS_H
#define CPROVER_SOLVERS_FLATTENING_FUNCTIONS_H

#include <set>

#include <util/mathematical_expr.h>

#include <solvers/prop/prop_conv.h>

class functionst
{
public:
  explicit functionst(prop_convt &_prop_conv):
    prop_conv(_prop_conv) { }

  virtual ~functionst()
  {
  }

  void record(
    const function_application_exprt &function_application);

  virtual void post_process()
  {
    add_function_constraints();
  }

protected:
  prop_convt &prop_conv;

  typedef std::set<function_application_exprt> applicationst;

  struct function_infot
  {
    applicationst applications;
  };

  typedef std::map<exprt, function_infot> function_mapt;
  function_mapt function_map;

  virtual void add_function_constraints();
  virtual void add_function_constraints(const function_infot &info);

  exprt arguments_equal(const exprt::operandst &o1,
                        const exprt::operandst &o2);
};

#endif // CPROVER_SOLVERS_FLATTENING_FUNCTIONS_H
