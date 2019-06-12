/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// goto_statet class definition

#ifndef CPROVER_GOTO_SYMEX_GOTO_STATE_H
#define CPROVER_GOTO_SYMEX_GOTO_STATE_H

#include <util/sharing_map.h>

#include <analyses/guard.h>
#include <analyses/local_safe_pointers.h>

#include "renaming_level.h"
#include "symex_value_set.h"

/// Container for data that varies per program point, e.g. the constant
/// propagator state, when state needs to branch. This is copied out of
/// goto_symex_statet at a control-flow fork and then back into it at a
/// control-flow merge.
class goto_statet
{
public:
  /// Distance from entry
  unsigned depth = 0;

protected:
  symex_level2t level2;

public:
  const symex_level2t &get_level2() const
  {
    return level2;
  }

  /// Uses level 1 names, and is used to do dereferencing
  symex_value_sett value_set;

  // A guard is a particular condition that has to pass for an instruction
  // to be executed. The easiest example is an if/else: each instruction along
  // the if branch will be guarded by the condition of the if (and if there
  // is an else branch then instructions on it will be guarded by the negation
  // of the condition of the if).
  guardt guard;

  // Map L1 names to (L2) constants. Values will be evicted from this map
  // when they become non-constant. This is used to propagate values that have
  // been worked out to only have one possible value.
  //
  // "constants" can include symbols, but only in the context of an address-of
  // op (i.e. &x can be propagated), and an address-taken thing should only be
  // L1.
  sharing_mapt<irep_idt, exprt> propagation;

  void output_propagation_map(std::ostream &);

  /// Threads
  unsigned atomic_section_id = 0;

  /// Constructors
  goto_statet() = delete;
  goto_statet &operator=(const goto_statet &other) = delete;
  goto_statet &operator=(goto_statet &&other) = default;
  goto_statet(const goto_statet &other) = default;
  goto_statet(goto_statet &&other) = default;

  explicit goto_statet(const class goto_symex_statet &s);

  explicit goto_statet(guard_managert &guard_manager)
    : guard(true_exprt(), guard_manager)
  {
  }

  void apply_condition(
    const exprt &condition, // L2
    const goto_symex_statet &previous_state,
    const namespacet &ns);

  std::size_t increase_generation(
    const irep_idt l1_identifier,
    const ssa_exprt &lhs,
    std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider);
};

#endif // CPROVER_GOTO_SYMEX_GOTO_STATE_H
