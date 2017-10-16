/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set Propagation

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H

#define USE_DEPRECATED_STATIC_ANALYSIS_H
#include <analyses/static_analysis.h>

#include "value_set_domain.h"
#include "value_sets.h"

class xmlt;

class value_set_analysist:
  public value_setst,
  public static_analysist<value_set_domaint>
{
public:
  explicit value_set_analysist(const namespacet &_ns):
    static_analysist<value_set_domaint>(_ns)
  {
  }

  typedef static_analysist<value_set_domaint> baset;

  // overloading
  virtual void initialize(const goto_programt &goto_program);
  virtual void initialize(const goto_functionst &goto_functions);

  void convert(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const;

public:
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    (*this)[l].value_set.get_value_set(expr, dest, ns);
  }
};

void convert(
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

void convert(
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
