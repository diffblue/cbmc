/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com
        Alex Horn, alex.horn@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_PATH_SEARCH_H
#define CPROVER_PATH_SEARCH_H

#include <util/time_stopping.h>

#include <goto-programs/safety_checker.h>

#include <aa-path-symex/path_symex_state.h>

class path_searcht:public safety_checkert
{
public:
  explicit inline path_searcht(const namespacet &_ns):
    safety_checkert(_ns),
    show_vcc(false),
    depth_limit(-1), // no limit
    context_bound(-1),
    unwind_limit(-1)
  {
  }

  virtual resultt operator()(
    const goto_functionst &goto_functions);

  bool show_vcc;
  
  unsigned depth_limit;
  unsigned context_bound;
  unsigned unwind_limit;

  // statistics
  unsigned number_of_paths;
  unsigned number_of_instructions;
  unsigned number_of_dropped_states;
  unsigned number_of_VCCs;
  unsigned number_of_VCCs_after_simplification;
  unsigned number_of_failed_properties;
  unsigned number_of_fast_forward_steps;
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

#ifdef PATH_SYMEX_FORK
  // blocks until child processes have terminated
  int await();

  // returns whether at least one child process has terminated
  bool try_await();
#endif

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
};

#endif
