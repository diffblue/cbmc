/*******************************************************************\

Module: Value Set Propagation (flow insensitive)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FI_H
#define CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FI_H

#include <goto-programs/flow_insensitive_analysis.h>

#include "value_set_domain_fi.h"
#include "value_sets.h"

class value_set_analysis_fit :
  public value_setst,
  public flow_insensitive_analysist<value_set_domain_fit>
{
public:  
  enum track_optionst { TRACK_ALL_POINTERS, TRACK_FUNCTION_POINTERS };
  
  // constructor
  value_set_analysis_fit(
    const namespacet &_ns,
    track_optionst _track_options=TRACK_ALL_POINTERS):
      flow_insensitive_analysist<value_set_domain_fit>(_ns),
      track_options(_track_options)
  {
  }
    
  typedef flow_insensitive_analysist<value_set_domain_fit> baset;

  virtual void initialize(const goto_programt &goto_program);
  virtual void initialize(const goto_functionst &goto_functions);
  
protected:
  track_optionst track_options;
  
  bool check_type(const typet &type);
  void get_globals(std::list<value_set_fit::entryt> &dest);
  void add_vars(const goto_functionst &goto_functions);
  void add_vars(const goto_programt &goto_programa);

  void get_entries(
    const symbolt &symbol,
    std::list<value_set_fit::entryt> &dest);

  void get_entries_rec(
    const irep_idt &identifier,
    const std::string &suffix,
    const typet &type,
    std::list<value_set_fit::entryt> &dest);
  
public:
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    std::list<exprt> &dest)
  {
    state.value_set.from_function = 
      state.value_set.function_numbering.number(l->function);
    state.value_set.to_function = 
      state.value_set.function_numbering.number(l->function);
    state.value_set.from_target_index = l->location_number;
    state.value_set.to_target_index = l->location_number;
    state.value_set.get_value_set(expr, dest, ns);
  }  
};

#endif /*VALUE_PROPAGATION_FUI_H_*/
