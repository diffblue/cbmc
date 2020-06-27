/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Track function-local control flow for loop unwinding and path senstivity

#ifndef CPROVER_ANALYSES_LOCAL_CONTROL_FLOW_HISTORY_H
#define CPROVER_ANALYSES_LOCAL_CONTROL_FLOW_HISTORY_H

#include "ai_history.h"

/// Records all local control-flow decisions up to a limit of number of
/// histories per location.  This gives a linear scaling between history limits
/// and space and time used.  Note this does no interprocedural context so all
/// calls will be merged to a single start point.

/// The history is stored as a (shared) list of decisions, effectively a tree
class local_control_flow_decisiont
{
public:
  typedef ai_history_baset::locationt locationt;
  locationt branch_location;
  bool branch_taken;
  typedef std::shared_ptr<const local_control_flow_decisiont> lcfd_ptrt;
  lcfd_ptrt previous; // null at the start of the function

  local_control_flow_decisiont(locationt loc, bool taken, lcfd_ptrt ptr)
    : branch_location(loc), branch_taken(taken), previous(ptr)
  {
  }

  bool operator<(const local_control_flow_decisiont &op) const;
  bool operator==(const local_control_flow_decisiont &op) const;
};

/// Whether we track forwards and / or backwards jumps is compile-time fixed
/// as it does not need to be variable and because there may be a *lot* of
/// history objects created
template <bool track_forward_jumps, bool track_backward_jumps>
class local_control_flow_historyt : public ai_history_baset
{
protected:
  typedef local_control_flow_decisiont::lcfd_ptrt lcfd_ptrt;

  locationt current_loc;
  lcfd_ptrt control_flow_decision_history;
  size_t max_histories_per_location;

  // A repeating idiom -- can cast from interface type to this type
  // caller's responsibility to ensure correct types
  std::shared_ptr<const local_control_flow_historyt<
    track_forward_jumps,
    track_backward_jumps>>
  to_local_control_flow_history(trace_ptrt in) const
  {
    PRECONDITION(in != nullptr);
    auto tmp = std::dynamic_pointer_cast<const local_control_flow_historyt<
      track_forward_jumps,
      track_backward_jumps>>(in);
    PRECONDITION(tmp != nullptr);
    return tmp;
  }

public:
  // nullptr denotes this is the "merge all other CFG paths" node
  bool is_path_merge_history(void) const
  {
    return control_flow_decision_history == nullptr;
  }

  // Set to 0 to disable but be aware that this may well diverge
  // and not terminate
  bool has_histories_per_location_limit(void) const
  {
    return max_histories_per_location != 0;
  }

  explicit local_control_flow_historyt(locationt loc)
    : ai_history_baset(loc),
      current_loc(loc),
      control_flow_decision_history(
        std::make_shared<local_control_flow_decisiont>(loc, true, nullptr)),
      max_histories_per_location(0)
  {
  }

  local_control_flow_historyt(locationt loc, lcfd_ptrt hist, size_t max_hist)
    : ai_history_baset(loc),
      current_loc(loc),
      control_flow_decision_history(hist),
      max_histories_per_location(max_hist)
  {
  }

  local_control_flow_historyt(locationt loc, size_t max_hist)
    : ai_history_baset(loc),
      current_loc(loc),
      control_flow_decision_history(
        std::make_shared<local_control_flow_decisiont>(loc, true, nullptr)),
      max_histories_per_location(max_hist)
  {
  }

  local_control_flow_historyt(
    const local_control_flow_historyt<track_forward_jumps, track_backward_jumps>
      &old)
    : ai_history_baset(old.current_loc),
      current_loc(old.current_loc),
      control_flow_decision_history(old.control_flow_decision_history),
      max_histories_per_location(old.max_histories_per_location)
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
    return current_loc;
  }

  // If there is no history, then it is because we have merged
  // If we are merging control flow histories then we should probably
  // also widen on domain merge so that analysis converges faster.
  bool should_widen(const ai_history_baset &other) const override
  {
    return is_path_merge_history();
  }

  void output(std::ostream &out) const override;
};

// Sets the kind of jumps to track and the max number of histories per location
class local_control_flow_history_factoryt : public ai_history_factory_baset
{
protected:
  bool track_forward_jumps;
  bool track_backward_jumps;
  size_t max_histories_per_location;

public:
  local_control_flow_history_factoryt(
    bool track_f,
    bool track_b,
    size_t max_hist)
    : track_forward_jumps(track_f),
      track_backward_jumps(track_b),
      max_histories_per_location(max_hist)
  {
  }

  ai_history_baset::trace_ptrt epoch(ai_history_baset::locationt l) override
  {
    if(track_forward_jumps)
    {
      if(track_backward_jumps)
      {
        // All local control flow branches
        return std::make_shared<local_control_flow_historyt<true, true>>(
          l, max_histories_per_location);
      }
      else
      {
        // "Path sensitive" but merge loops eagerly
        return std::make_shared<local_control_flow_historyt<true, false>>(
          l, max_histories_per_location);
      }
    }
    else
    {
      if(track_backward_jumps)
      {
        // Loop unwinding but merge branches eagerly
        return std::make_shared<local_control_flow_historyt<false, true>>(
          l, max_histories_per_location);
      }
      else
      {
        // Ignore all branches.  Same effect as ahistorical but at more cost???
        return std::make_shared<local_control_flow_historyt<false, false>>(
          l, max_histories_per_location);
      }
    }
    UNREACHABLE;
  }

  virtual ~local_control_flow_history_factoryt()
  {
    // Pointer is reference counted.
  }
};

#endif // CPROVER_ANALYSES_LOCAL_CONTROL_FLOW_HISTORY_H
