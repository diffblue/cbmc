/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "remove_unreachable.h"

#include <set>
#include <stack>

/// remove unreachable code
void remove_unreachable(goto_programt &goto_program)
{
  std::set<goto_programt::targett> reachable;
  std::stack<goto_programt::targett> working;

  working.push(goto_program.instructions.begin());

  while(!working.empty())
  {
    goto_programt::targett t=working.top();
    working.pop();

    if(reachable.find(t)==reachable.end() &&
       t!=goto_program.instructions.end())
    {
      reachable.insert(t);

      for(const auto &succ : goto_program.get_successors(t))
        working.push(succ);
    }
  }

  // make all unreachable code a skip
  // unless it's an 'end_function'

  Forall_goto_program_instructions(it, goto_program)
  {
    if(reachable.find(it)==reachable.end() &&
       !it->is_end_function())
      it->make_skip();
  }
}

/// Removes unreachable instructions from all functions.
/// \par parameters: The goto functions from which the unreachable functions are
/// to be removed.
/// \return None.
void remove_unreachable(goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
    remove_unreachable(f_it->second.body);
}
