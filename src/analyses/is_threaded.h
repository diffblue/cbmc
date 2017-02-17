/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#ifndef CPROVER_ANALYSES_IS_THREADED_H
#define CPROVER_ANALYSES_IS_THREADED_H

#include <set>

#include <goto-programs/goto_functions.h>

class is_threadedt
{
public:
  explicit is_threadedt(
    const goto_functionst &goto_functions)
  {
    compute(goto_functions);
  }

  bool operator()(const goto_programt::const_targett t) const
  {
    return is_threaded_set.find(t)!=is_threaded_set.end();
  }

protected:
  typedef std::set<goto_programt::const_targett> is_threaded_sett;
  is_threaded_sett is_threaded_set;

  void compute(
    const goto_functionst &goto_functions);
};

#endif // CPROVER_ANALYSES_IS_THREADED_H
