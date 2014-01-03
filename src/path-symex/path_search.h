/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SEARCH_H
#define CPROVER_PATH_SEARCH_H

#include <goto-programs/safety_checker.h>

#include <path-symex/path_symex_state.h>

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

  unsigned number_of_dropped_states;

protected:
  typedef path_symex_statet statet;

  // State queue. Iterators are stable.
  typedef std::list<statet> queuet;
  queuet queue;
  
  queuet::iterator pick_state();
  
  bool execute(queuet::iterator state, const namespacet &);
  
  bool check_assertion(statet &state, const namespacet &);
  void do_show_vcc(statet &state, const namespacet &);
  
  bool drop_state(const statet &state) const;
};

#endif
