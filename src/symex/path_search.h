/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SEARCH_H
#define CPROVER_PATH_SEARCH_H

#include <util/time_stopping.h>

#include <goto-programs/safety_checker.h>

#include <path-symex/path_symex_state.h>

class path_searcht:public safety_checkert
{
public:
  explicit inline path_searcht(const namespacet &_ns):
    safety_checkert(_ns),
    show_vcc(false),
    depth_limit_set(false), // no limit
    context_bound_set(false),
    unwind_limit_set(false)
  {
  }

  virtual resultt operator()(
    const goto_functionst &goto_functions);
    
  void set_depth_limit(unsigned limit)
  {
    depth_limit_set=true;
    depth_limit=limit;
  }

  void set_context_bound(unsigned limit)
  {
    context_bound_set=true;
    context_bound=limit;
  }

  void set_unwind_limit(unsigned limit)
  {
    unwind_limit_set=true;
    unwind_limit=limit;
  }

  bool show_vcc;
  
  // statistics
  unsigned number_of_dropped_states;
  unsigned number_of_paths;
  unsigned number_of_steps;
  unsigned number_of_VCCs;
  unsigned number_of_VCCs_after_simplification;
  unsigned number_of_failed_properties;
  absolute_timet start_time;
  time_periodt sat_time;

  enum statust { NOT_REACHED, PASS, FAIL };

  struct property_entryt
  {
    statust status;
    irep_idt description;
    goto_tracet error_trace;
  };
  
  typedef std::map<irep_idt, property_entryt> property_mapt;
  property_mapt property_map;

protected:
  typedef path_symex_statet statet;

  // State queue. Iterators are stable.
  typedef std::list<statet> queuet;
  queuet queue;
  
  queuet::iterator pick_state();
  
  bool execute(queuet::iterator state, const namespacet &);
  
  void check_assertion(statet &state, const namespacet &);
  void do_show_vcc(statet &state, const namespacet &);
  
  bool drop_state(const statet &state) const;
  
  void report_statistics();
  
  void initialize_property_map(
    const goto_functionst &goto_functions);

  unsigned depth_limit;
  unsigned context_bound;
  unsigned unwind_limit;
  bool depth_limit_set, context_bound_set, unwind_limit_set;
};

#endif
