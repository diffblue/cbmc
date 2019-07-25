/*******************************************************************\

Module: Symbolic Execution

Author: John Dumbell

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_COMPLEXITY_LIMITER_H
#define CPROVER_GOTO_SYMEX_COMPLEXITY_LIMITER_H

#include "complexity_violation.h"
#include "goto_symex_state.h"
#include "symex_complexity_limit_exceeded_action.h"

/// Symex complexity module.
///
/// Dynamically sets branches as unreachable symex considers them too complex.
/// A branch is too complex when runtime may be beyond reasonable
/// bounds due to internal structures becoming too large or solving conditions
/// becoming too big for the SAT solver to deal with.
///
/// On top of the branch cancelling there is special consideration for loops.
/// As branches get cancelled it keeps track of what loops are currently active
/// up through the stack. If a loop has too many of its child branches killed
/// (including additional loops or recursion) it won't do any more unwinds of
/// that particular loop and will blacklist it.
///
/// This blacklist is only held for as long as any loop is still active. As soon
/// as the loop iteration ends and the context in which the code is being
/// executed changes it'll be able to be run again.
///
/// Example of loop blacklisting:
///
///     loop A: (complexity: 5070)
///         loop B: (complexity: 5000)
///         loop C: (complexity: 70)
///
/// In the above loop B will be blacklisted if we have a complexity limitation
/// < 5000, but loop A and C will still be run, because when loop B is removed
/// the complexity of the loop as a whole is acceptable.
class complexity_limitert
{
public:
  complexity_limitert() = default;

  complexity_limitert(message_handlert &logger, const optionst &options);

  /// Is the complexity module active?
  /// \return Whether complexity limits are active or not.
  inline bool complexity_limits_active()
  {
    return this->complexity_active;
  }

  /// Checks the passed-in state to see if its become too complex for us to deal
  /// with, and if so set its guard to false.
  /// \param state goto_symex_statet you want to check the complexity of.
  /// \return True/false depending on whether this branch should be abandoned.
  complexity_violationt check_complexity(goto_symex_statet &state);

  /// Runs a suite of transformations on the state and symex executable,
  /// performing whatever transformations are required depending on
  /// the modules that have been loaded.
  void run_transformations(
    complexity_violationt complexity_violation,
    goto_symex_statet &current_state);

protected:
  mutable messaget log;

  /// Is the complexity module active, usually coincides with a max_complexity
  /// value above 0.
  bool complexity_active = false;

  /// Functions called when the heuristic has been violated. Can perform
  /// any form of branch, state or full-program transformation.
  std::vector<symex_complexity_limit_exceeded_actiont>
    violation_transformations;

  /// Default heuristic transformation. Sets state as unreachable.
  symex_complexity_limit_exceeded_actiont default_transformation;

  /// The max complexity rating that a branch can be before it's abandoned. The
  /// internal representation for computing complexity, has no relation to the
  /// argument passed in via options.
  std::size_t max_complexity = 0;

  /// The amount of branches that can fail within the scope of a loops execution
  /// before the entire loop is abandoned.
  std::size_t max_loops_complexity = 0;

  /// Checks whether the current loop execution stack has violated
  /// max_loops_complexity.
  bool are_loop_children_too_complicated(call_stackt &current_call_stack);

  /// Checks whether we're in a loop that is currently considered blacklisted,
  /// and shouldn't be executed.
  static bool in_blacklisted_loop(
    const call_stackt &current_call_stack,
    const goto_programt::const_targett &instr);

  /// Returns inner-most currently active loop. This is frame-agnostic, so if
  /// we're in a loop further up the stack that will still be returned as
  /// the 'active' one.
  static framet::active_loop_infot *
  get_current_active_loop(call_stackt &current_call_stack);
};

#endif // CPROVER_GOTO_SYMEX_COMPLEXITY_LIMITER_H
