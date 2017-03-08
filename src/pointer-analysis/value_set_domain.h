/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#define USE_DEPRECATED_STATIC_ANALYSIS_H
#include <analyses/static_analysis.h>

#include "value_set.h"

template<class Value_Sett>
class value_set_domaint:public domain_baset
{
public:
  Value_Sett value_set;

  // overloading

  bool merge(const value_set_domaint &other, locationt to)
  {
    return value_set.make_union(other.value_set);
  }

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    value_set.output(ns, out);
  }

  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
    value_set.clear();
    value_set.location_number=l->location_number;
    value_set.function=l->function;
  }

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    value_set.get_reference_set(expr, dest, ns);
  }

  virtual void transform(
    const namespacet &ns,
    locationt from_l,
    locationt to_l)
  {
    switch(from_l->type)
    {
    case GOTO:
      // ignore for now
      break;

    case END_FUNCTION:
      value_set.do_end_function(static_analysis_baset::get_return_lhs(to_l), ns);
      break;

    case RETURN:
    case OTHER:
    case ASSIGN:
    case DECL:
    case DEAD:
      value_set.apply_code(from_l->code, ns);
      break;

    case ASSUME:
      value_set.guard(from_l->guard, ns);
      break;

    case FUNCTION_CALL:
      {
        const code_function_callt &code=
          to_code_function_call(from_l->code);

        value_set.do_function_call(to_l->function, code.arguments(), ns);
      }
    break;

    default:
      {
        // do nothing
      }
    }
  }
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
