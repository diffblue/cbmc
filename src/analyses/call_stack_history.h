/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// History for tracking the call stack and performing interprocedural analysis

#ifndef CPROVER_ANALYSES_CALL_STACK_HISTORY_H
#define CPROVER_ANALYSES_CALL_STACK_HISTORY_H

#include "ai_history.h"

/// Records the call stack
/// Care must be taken when using this on recursive code; it will need the
/// domain to be capable of limiting the recursion.
class call_stack_historyt : public ai_history_baset
{
protected:
  class call_stack_entryt;
  typedef std::shared_ptr<const call_stack_entryt> cse_ptrt;
  class call_stack_entryt
  {
  public:
    locationt current_location;
    cse_ptrt caller;

    call_stack_entryt(locationt l, cse_ptrt p) : current_location(l), caller(p)
    {
    }

    bool operator<(const call_stack_entryt &op) const;
    bool operator==(const call_stack_entryt &op) const;
  };

  cse_ptrt current_stack;
  // DATA_INVARIANT(current_stack != nullptr, "current_stack must exist");
  // DATA_INVARIANT(current_stack->current.is_dereferenceable(),
  //                "Must not be _::end()")

  // At what point to merge with a previous call stack when handling recursion
  // Setting to 0 disables completely
  unsigned int recursion_limit;

  bool has_recursion_limit(void) const
  {
    return recursion_limit != 0;
  }

  call_stack_historyt(cse_ptrt cur_stack, unsigned int rec_lim)
    : ai_history_baset(cur_stack->current_location),
      current_stack(cur_stack),
      recursion_limit(rec_lim)
  {
    PRECONDITION(
      cur_stack != nullptr); // A little late by now but worth documenting
  }

public:
  explicit call_stack_historyt(locationt l)
    : ai_history_baset(l),
      current_stack(std::make_shared<call_stack_entryt>(l, nullptr)),
      recursion_limit(0)
  {
  }

  call_stack_historyt(locationt l, unsigned int rec_lim)
    : ai_history_baset(l),
      current_stack(std::make_shared<call_stack_entryt>(l, nullptr)),
      recursion_limit(rec_lim)
  {
  }

  call_stack_historyt(const call_stack_historyt &old)
    : ai_history_baset(old),
      current_stack(old.current_stack),
      recursion_limit(old.recursion_limit)
  {
  }

  step_returnt step(
    locationt to,
    const trace_sett &others,
    trace_ptrt caller_hist) const override;

  bool operator<(const ai_history_baset &op) const override;
  bool operator==(const ai_history_baset &op) const override;

  const locationt &current_location(void) const override
  {
    return current_stack->current_location;
  }

  // Use default widening
  // Typically this would be used for loops, which are not tracked
  // it would be possible to use this to improve the handling of recursion
  bool should_widen(const ai_history_baset &other) const override
  {
    return ai_history_baset::should_widen(other);
  }

  void output(std::ostream &out) const override;
};

// Allows passing a recursion limit
class call_stack_history_factoryt : public ai_history_factory_baset
{
protected:
  unsigned int recursion_limit;

public:
  explicit call_stack_history_factoryt(unsigned int rec_lim)
    : recursion_limit(rec_lim)
  {
  }

  ai_history_baset::trace_ptrt epoch(ai_history_baset::locationt l) override
  {
    ai_history_baset::trace_ptrt p(
      std::make_shared<call_stack_historyt>(l, recursion_limit));
    return p;
  }

  virtual ~call_stack_history_factoryt()
  {
  }
};

#endif // CPROVER_ANALYSES_CALL_STACK_HISTORY_H
