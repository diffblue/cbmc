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

void value_sets_to_xml(
  std::function<const value_sett &(goto_programt::const_targett)> get_value_set,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  xmlt &dest);

template<class VSDT>
class value_set_analysis_templatet:
  public value_setst,
  public static_analysist<VSDT>
{
public:
  typedef VSDT domaint;
  typedef static_analysist<domaint> baset;
  typedef typename baset::locationt locationt;

  explicit value_set_analysis_templatet(const namespacet &ns):baset(ns)
  {
  }

  void convert(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const
  {
    value_sets_to_xml(
      [this](locationt l) { return (*this)[l].value_set; },
      goto_program,
      identifier,
      dest);
  }

public:
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    (*this)[l].value_set.get_value_set(expr, dest, baset::ns);
  }
};

typedef
  value_set_analysis_templatet<value_set_domain_templatet<value_sett>>
  value_set_analysist;

void convert(
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

void convert(
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
