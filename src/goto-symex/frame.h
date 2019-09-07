/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Class for stack frames

#ifndef CPROVER_GOTO_SYMEX_FRAME_H
#define CPROVER_GOTO_SYMEX_FRAME_H

#include "goto_state.h"
#include "symex_target.h"

/// Stack frames -- these are used for function calls and for exceptions
struct framet
{
  // gotos
  using goto_state_listt =
    std::list<std::pair<symex_targett::sourcet, goto_statet>>;

  // function calls
  irep_idt function_identifier;
  std::map<goto_programt::const_targett, goto_state_listt> goto_state_map;
  symex_targett::sourcet calling_location;
  std::vector<irep_idt> parameter_names;
  guardt guard_at_function_start;
  goto_programt::const_targett end_of_function;
  exprt return_value = nil_exprt();
  bool hidden_function = false;

  symex_level1t old_level1;

  std::set<irep_idt> local_objects;

  // exceptions
  std::map<irep_idt, goto_programt::targett> catch_map;

  // loop and recursion unwinding
  struct loop_infot
  {
    unsigned count = 0;
    bool is_recursion = false;
  };

  std::unordered_map<irep_idt, loop_infot> loop_iterations;

  std::unordered_map<goto_programt::const_targett, guardt, const_target_hash>
    instruction_guards;

  framet(symex_targett::sourcet _calling_location, const guardt &state_guard)
    : calling_location(std::move(_calling_location)),
      guard_at_function_start(state_guard)
  {
  }
};

#endif // CPROVER_GOTO_SYMEX_FRAME_H
