/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FIVR_H
#define CPROVER_POINTER_ANALYSIS_VALUE_PROPAGATION_FIVR_H

#include <goto-programs/flow_insensitive_analysis.h>

#include "value_set_domain_fivr.h"
#include "value_sets.h"

class value_set_analysis_fivrt : 
  public value_setst,
  public flow_insensitive_analysist<value_set_domain_fivrt>
{
public:
  enum track_optionst { TRACK_ALL_POINTERS, TRACK_FUNCTION_POINTERS };
  
  // constructor
  value_set_analysis_fivrt(
    const namespacet &_ns, 
    track_optionst _track_options=TRACK_ALL_POINTERS):
    flow_insensitive_analysist<value_set_domain_fivrt>(_ns),
    track_options(_track_options)
  {
  }
    
  typedef flow_insensitive_analysist<value_set_domain_fivrt> baset;

  virtual void initialize(const goto_programt &goto_program);
  virtual void initialize(const goto_functionst &goto_functions);

  void output(locationt l, std::ostream &out) 
  {
    state.value_set.set_from(l->function, l->location_number);
    state.value_set.set_to(l->function, l->location_number);    
    state.output(ns, out);
  }
  
  void output(const goto_programt &goto_program, std::ostream &out)
  {
    forall_goto_program_instructions(it, goto_program)
    {
      std::cout << "**** " << it->location << std::endl;      
      output(it, out);
      std::cout << std::endl;
      goto_program.output_instruction(ns, "", std::cout, it);
      std::cout << std::endl;
    }
  }
  
protected:
  track_optionst track_options;
  
  bool check_type(const typet &type);
  void get_globals(std::list<value_set_fivrt::entryt> &dest);
  void add_vars(const goto_functionst &goto_functions);
  void add_vars(const goto_programt &goto_programa);

  void get_entries(
    const symbolt &symbol,
    std::list<value_set_fivrt::entryt> &dest);

  void get_entries_rec(
    const irep_idt &identifier,
    const std::string &suffix,
    const typet &type,
    std::list<value_set_fivrt::entryt> &dest);
  
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

#endif /*VALUE_PROPAGATION_INCR_H_*/
