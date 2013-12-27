/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SEARCH_H
#define CPROVER_PATH_SEARCH_H

#include <util/message.h>

#include <goto-programs/goto_model.h>

#include <path-symex/path_symex_state.h>

class path_searcht:public messaget
{
public:
  inline path_searcht()
  {
  }

  bool operator()(
    const symbol_tablet &symbol_table,
    const goto_functionst &goto_functions);

protected:
  typedef path_symex_statet statet;

  typedef std::list<statet> queuet;
  queuet queue;
  
  queuet::iterator pick_state();
  
  bool execute(queuet::iterator state, const namespacet &);
  
  bool check_assertion(const statet &state, const namespacet &);
};

#endif
