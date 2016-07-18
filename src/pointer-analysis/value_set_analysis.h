/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H

#include <iostream>

#include <analyses/ai.h>

#include "value_set_domain.h"
#include "value_sets.h"

class xmlt;

class value_set_analysist:
  public value_setst,
  public concurrency_aware_ait<value_set_domaint>
{
public:
  
  value_set_analysist(bool _use_top=false)
   : concurrency_aware_ait<value_set_domaint>(),
     use_top(_use_top) // set per-variable object maps in value_set
                       //   to top as soon as they contain an "unknown" object
   {
   }

  typedef concurrency_aware_ait<value_set_domaint> baset;

  // overloading  

  virtual void convert(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    xmlt &dest);

  virtual void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    xmlt &dest);

  void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const;
    
  virtual void statistics(std::ostream &out) const;
      
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns)
  {
    (*this)[l].value_set.get_value_set(expr, dest, ns);
  }  

  virtual void show(
    const namespacet &ns,
    ui_message_handlert::uit ui,
    const goto_functionst &goto_functions)
  {
    baset::show(ns, ui, goto_functions);
    if(ui==ui_message_handlert::PLAIN)
      statistics(std::cout);
  }

  virtual void show(
    const namespacet &ns,
    ui_message_handlert::uit ui,
    const goto_programt &goto_program) 
  {
    baset::show(ns, ui, goto_program);
    if(ui==ui_message_handlert::PLAIN)
      statistics(std::cout);
  }

protected:
  bool use_top;

  virtual statet &get_state(locationt l)
  {
    statet &state = state_map[l];
    static_cast<value_set_domaint &>(state).value_set.use_top = use_top;
    return state;
  }

};

#endif
