/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_CALL_STACK_H
#define CPROVER_GOTO_SYMEX_CALL_STACK_H

#include "frame.h"

class call_stackt : public std::vector<framet>
{
public:
  framet &top()
  {
    PRECONDITION(!empty());
    return back();
  }

  const framet &top() const
  {
    PRECONDITION(!empty());
    return back();
  }

  framet &
  new_frame(symex_targett::sourcet calling_location, const guardt &guard)
  {
    emplace_back(calling_location, guard);
    return back();
  }

  void pop()
  {
    PRECONDITION(!empty());
    pop_back();
  }

  const framet &previous_frame()
  {
    return *(--(--end()));
  }
};

#endif // CPROVER_GOTO_SYMEX_CALL_STACK_H
