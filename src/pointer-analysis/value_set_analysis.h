/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H

#define USE_DEPRECATED_STATIC_ANALYSIS_H
#include <analyses/static_analysis.h>
#include <util/xml_expr.h>
#include <util/xml.h>
#include <util/expr_util.h>

#include "value_set_domain.h"
#include "value_sets.h"
#include "value_set.h"

class xmlt;

template<class Value_Sett>
class value_set_analysis_baset:
  public value_setst,
  public static_analysist<value_set_domaint<Value_Sett> >
{
public:
  typedef value_set_domaint<Value_Sett> domaint;
  typedef static_analysist<domaint> baset;
  typedef typename baset::locationt locationt;

  explicit value_set_analysis_baset(const namespacet &_ns):baset(_ns)
  {
  }

  // overloading
  void initialize(const goto_programt &goto_program)
  {
    baset::initialize(goto_program);
  }
  void initialize(const goto_functionst &goto_functions)
  {
    baset::initialize(goto_functions);
  }

  void convert(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const
  {
    source_locationt previous_location;

    forall_goto_program_instructions(i_it, goto_program)
    {
      const source_locationt &location=i_it->source_location;

      if(location==previous_location)
        continue;

      if(location.is_nil() || location.get_file()==irep_idt())
        continue;

      // find value set
      const value_sett &value_set=(*this)[i_it].value_set;

      xmlt &i=dest.new_element("instruction");
      i.new_element()=::xml(location);

      for(value_sett::valuest::const_iterator
            v_it=value_set.values.begin();
          v_it!=value_set.values.end();
          v_it++)
      {
        xmlt &var=i.new_element("variable");
        var.new_element("identifier").data=
          id2string(v_it->first);

#if 0
        const value_sett::expr_sett &expr_set=
          v_it->second.expr_set();

        for(value_sett::expr_sett::const_iterator
              e_it=expr_set.begin();
            e_it!=expr_set.end();
            e_it++)
        {
          std::string value_str=
            from_expr(ns, identifier, *e_it);

          var.new_element("value").data=
            xmlt::escape(value_str);
        }
#endif
      }
    }
  }

public:
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest)
  {
    ((const value_sett&)(*this)[l].value_set).get_value_set(
      expr,
      dest,
      baset::ns);
  }

  /*******************************************************************\

  Function: value_set_analysis_baset::is_singular

    Inputs: The set of expressions to check.

   Outputs: true, if it contains only one expression and 
            that expression is a symbol, 
            false, otherwise.

   Purpose: Get whether a set of expressions can have a strong update
            or not.

  \*******************************************************************/

  virtual bool is_singular(const std::set<exprt> &values)
  {
    return values.size()==1 && values.begin()->id()==ID_symbol;
  }
};

typedef value_set_analysis_baset<value_sett> value_set_analysist;

void convert(
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

void convert(
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
