/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DOMAIN_H

#define USE_DEPRECATED_STATIC_ANALYSIS_H
#include <analyses/static_analysis.h>

#include "value_set.h"

template<class> class value_set_domaint;

// Forwarders for value_set_domaint's calls against value_sett.
// Specialise these if for some reason you can't just write a member function,
// or for location numbers, expose the field.
template<typename VST>
inline bool value_set_make_union(VST &value_set, const VST &other)
{
  return value_set.make_union(other);
}

template<typename VST>
inline void value_set_output(
  const VST &value_set, const namespacet &ns, std::ostream &out)
{
  value_set.output(ns, out);
}

template<typename VST>
inline void value_set_clear(VST &value_set)
{
  value_set.clear();
}

template<typename VST>
inline void value_set_set_location_number(VST &value_set, unsigned loc)
{
  value_set.location_number=loc;
}

template<typename VST>
inline void value_set_read_reference_set(
  const VST &value_set,
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns)
{
  value_set.read_reference_set(expr, dest, ns);
}

template<typename VST>
inline void value_set_do_end_function(
  VST &value_set, const exprt &return_expr, const namespacet &ns)
{
  value_set.do_end_function(return_expr, ns);
}

template<typename VST>
inline void value_set_apply_code(
  VST &value_set, const codet &code, const namespacet &ns)
{
  value_set.apply_code(code, ns);
}

template<typename VST>
inline void value_set_guard(
  VST &value_set, const exprt &guard, const namespacet &ns)
{
  value_set.guard(guard, ns);
}

template<typename VST>
inline void value_set_do_function_call(
  VST &value_set,
  const irep_idt &function,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  value_set.do_function_call(function, arguments, ns);
}

template<class VST>
class value_set_domaint:public domain_baset
{
public:
  VST value_set;

  // overloading

  bool merge(const value_set_domaint<VST> &other, locationt to)
  {
    return value_set_make_union(value_set, other.value_set);
  }

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    value_set_output(value_set, ns, out);
  }

  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
    value_set_clear(value_set);
    value_set.location_number=l->location_number;
  }

  virtual void get_reference_set(
    const namespacet &ns,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    value_set_read_reference_set(value_set, expr, dest, ns);
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
    {
      value_set_do_end_function(
        value_set, static_analysis_baset::get_return_lhs(to_l), ns);
      break;
    }

    // Note intentional fall-through here:
    case RETURN:
    case OTHER:
    case ASSIGN:
    case DECL:
    case DEAD:
      value_set_apply_code(value_set, from_l->code, ns);
      break;

    case ASSUME:
      value_set_guard(value_set, from_l->guard, ns);
      break;

    case FUNCTION_CALL:
      {
        const code_function_callt &code=
          to_code_function_call(from_l->code);

        value_set_do_function_call(
          value_set, to_l->function, code.arguments(), ns);
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
