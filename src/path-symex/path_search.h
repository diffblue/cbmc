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
    show_vcc(false)
  {
  }

  virtual resultt operator()(
    const goto_functionst &goto_functions);

  bool show_vcc;

protected:
  typedef path_symex_statet statet;

  typedef std::list<statet> queuet;
  queuet queue;
  
  queuet::iterator pick_state();
  
  bool execute(queuet::iterator state, const namespacet &);
  
  bool check_assertion(statet &state, const namespacet &);
  void do_show_vcc(statet &state, const namespacet &);
};

#endif
