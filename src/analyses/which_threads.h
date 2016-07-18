/*******************************************************************\

Module: Which-Threads Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_WHICH_THREADS_H
#define CPROVER_ANALYSES_WHICH_THREADS_H

#include "which_threads_internal.h"

class which_threadst : protected which_threads_internalt
{

public:
  explicit which_threadst(const goto_functionst& _goto_functions)
  : which_threads_internalt(_goto_functions) {}

  // instruction is affected by concurrency
  bool is_threaded(const goto_programt::const_targett t) const
  {
    const goto_programt::instructiont &i=*t;

    if(i.is_assign()||i.is_goto())
      return which_threads_internalt::is_threaded(t);
    return false;
  }

  // instruction could be executed by more than one thread
  bool is_shared(const goto_programt::const_targett t) const
  {
    return which_threads_internalt::is_shared(t);
  }

  // instructions could be executed by two different threads
  bool are_concurrent(const goto_programt::const_targett t1,
    const goto_programt::const_targett t2)
  {
    return which_threads_internalt::are_concurrent(t1, t2);
  }

  void output_dot(std::ostream &out) const
  {
    which_threads_internalt::output_dot(out);
  }
  
  void output(std::ostream &out) const
  {
    which_threads_internalt::output(out);
  }
  
  void output_xml(std::ostream &out) const
  {
    which_threads_internalt::output_xml(out);
  }
};

#endif
