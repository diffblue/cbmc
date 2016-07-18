/*******************************************************************\

Module: Value Set Propagation (flow insensitive)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FI_H
#define CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FI_H

#include <analyses/flow_insensitive_analysis.h>

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
    track_optionst _track_options=TRACK_ALL_POINTERS):
      flow_insensitive_analysist<value_set_domain_fit>(),
      track_options(_track_options)
  {
  }
    
  typedef flow_insensitive_analysist<value_set_domain_fit> baset;

protected:
  track_optionst track_options;
  
  virtual void initialize(const goto_programt &goto_program, const namespacet &ns);
  virtual void initialize(const goto_functionst &goto_functions, const namespacet &ns);
  
  bool check_type(const typet &type,
		  const namespacet &ns);
  void get_globals(std::list<value_set_fit::entryt> &dest,
		   const namespacet &ns);
  void add_vars(const goto_functionst &goto_functions, const namespacet &ns);
  void add_vars(const goto_programt &goto_program, const namespacet &ns);

  void get_entries(
    const symbolt &symbol,
    std::list<value_set_fit::entryt> &dest,
    const namespacet &ns);

  void get_entries_rec(
    const irep_idt &identifier,
    const std::string &suffix,
    const typet &type,
    std::list<value_set_fit::entryt> &dest,
    const namespacet &ns);
  
public:
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    std::list<exprt> &dest,
    const namespacet &ns)
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

#endif /*CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FI_H_*/
