/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_IS_THREADED_H
#define CPROVER_GOTO_PROGRAMS_IS_THREADED_H

#include <set>

#include <goto-programs/goto_functions.h>

class is_threadedt
{
public:
  is_threadedt(
    const namespacet &_ns,
    const goto_functionst &goto_functions):
    ns(_ns)
  {
    compute(goto_functions);
  }

  inline bool operator()(const goto_programt::const_targett t) const
  {
    return is_threaded_set.find(t)!=is_threaded_set.end();
  }
  
protected:
  const namespacet &ns;

  typedef std::set<goto_programt::const_targett> is_threaded_sett;
  is_threaded_sett is_threaded_set;

  void compute(
    const goto_functionst &goto_functions);
};

#endif
