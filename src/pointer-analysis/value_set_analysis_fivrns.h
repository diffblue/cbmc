/*******************************************************************\

Module: Value Set Analysis (Flow Insensitive, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com,
        CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_VALUE_SET_ANALYSIS_FIVRNS_H_
#define __CPROVER_VALUE_SET_ANALYSIS_FIVRNS_H_

#include <goto-programs/flow_insensitive_analysis.h>

#include "value_set_domain_fivrns.h"
#include "value_sets.h"

class value_set_analysis_fivrnst : 
  public value_setst,
  public flow_insensitive_analysist<value_set_domain_fivrnst>
{
public:
  enum track_optionst { TRACK_ALL_POINTERS, TRACK_FUNCTION_POINTERS };
  
  // constructor
  value_set_analysis_fivrnst(
    const namespacet &_ns, 
    track_optionst _track_options=TRACK_ALL_POINTERS):
    flow_insensitive_analysist<value_set_domain_fivrnst>(_ns),
    track_options(_track_options)
  {
  }
    
  typedef flow_insensitive_analysist<value_set_domain_fivrnst> baset;

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
  void get_globals(std::list<value_set_fivrnst::entryt> &dest);
  void add_vars(const goto_functionst &goto_functions);
  void add_vars(const goto_programt &goto_programa);

  void get_entries(
    const symbolt &symbol,
    std::list<value_set_fivrnst::entryt> &dest);

  void get_entries_rec(
    const irep_idt &identifier,
    const std::string &suffix,
    const typet &type,
    std::list<value_set_fivrnst::entryt> &dest);
  
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

#endif /*__CPROVER_VALUE_SET_ANALYSIS_FIVRNS_H_*/
