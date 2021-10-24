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

#include <analyses/lexical_loops.h>

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
  exprt call_lhs = nil_exprt();                // cleaned, but not renamed
  optionalt<symbol_exprt> return_value_symbol; // not renamed
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

  class active_loop_infot
  {
  public:
    explicit active_loop_infot(lexical_loopst::loopt &_loop) : loop(_loop)
    {
    }

    /// Incremental counter on how many branches this loop has had killed.
    std::size_t children_too_complex = 0;

    /// Set of loop ID's that have been blacklisted.
    std::vector<std::reference_wrapper<lexical_loopst::loopt>>
      blacklisted_loops;

    // Loop information.
    lexical_loopst::loopt &loop;
  };

  std::shared_ptr<lexical_loopst> loops_info;
  std::vector<active_loop_infot> active_loops;

  std::unordered_map<irep_idt, loop_infot> loop_iterations;

  framet(symex_targett::sourcet _calling_location, const guardt &state_guard)
    : calling_location(std::move(_calling_location)),
      guard_at_function_start(state_guard)
  {
  }
};

#endif // CPROVER_GOTO_SYMEX_FRAME_H
