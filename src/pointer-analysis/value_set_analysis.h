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
  const std::function<const value_sett &(goto_programt::const_targett)>
    &get_value_set,
  const goto_programt &goto_program,
  xmlt &dest);

/// This template class implements a data-flow analysis which keeps track of
/// what values different variables might have at different points in the
/// program. It is used through the alias `value_set_analysist`, so `VSDT` is
/// `value_set_domain_templatet<value_sett>`.
///
/// Note: it is currently based on `static_analysist`, which is obsolete. It
/// should be moved onto `ait`.
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

  const value_sett &get_value_set(goto_programt::const_targett t)
  {
    return (*this)[t].value_set;
  }

  void convert(
    const goto_programt &goto_program,
    xmlt &dest) const
  {
    using std::placeholders::_1;
    value_sets_to_xml(
      std::bind(&value_set_analysis_templatet::get_value_set, *this, _1),
      goto_program,
      dest);
  }

public:
  // interface value_sets
  DEPRECATED(SINCE(2019, 05, 22, "use list returning version instead"))
  void get_values(
    const irep_idt &,
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest) override
  {
    (*this)[l].value_set.get_value_set(expr, dest, baset::ns);
  }

  // interface value_sets
  std::vector<exprt>
  get_values(const irep_idt &, locationt l, const exprt &expr) override
  {
    return (*this)[l].value_set.get_value_set(expr, baset::ns);
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
