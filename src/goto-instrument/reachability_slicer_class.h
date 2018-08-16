/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto Program Slicing

#ifndef CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H
#define CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include <analyses/is_threaded.h>

class slicing_criteriont;

class reachability_slicert
{
public:
  void operator()(
    goto_functionst &goto_functions,
    slicing_criteriont &criterion,
    bool include_forward_reachability)
  {
    cfg(goto_functions);
    is_threadedt is_threaded(goto_functions);
    fixedpoint_to_assertions(is_threaded, criterion);
    if(include_forward_reachability)
      fixedpoint_from_assertions(is_threaded, criterion);
    slice(goto_functions);
  }

protected:
  struct slicer_entryt
  {
    slicer_entryt()
      : backward_state(dfs_statust::NOT_SEEN),
        reachable_from_assertion(false)
    {
    }

    /// The status of each node during backwards depth-first traversal:
    /// A functions starts out NOT_SEEN, is raised to BODY_SEEN if we have seen
    /// a call to this function but know where it was called from (at this point
    /// we mark the function and anything reachable from it), then may finally
    /// be raised to BODY_AND_CALLERS_SEEN if we don't know what function calls
    /// this function, and therefore mark all of its callers as well.
    enum class dfs_statust
    {
      NOT_SEEN,
      BODY_SEEN,
      BODY_AND_CALLERS_SEEN
    } backward_state;
    bool reachable_from_assertion;
  };

  typedef cfg_baset<slicer_entryt> cfgt;
  cfgt cfg;

  typedef std::stack<cfgt::entryt> queuet;

  /// A search stack entry, used in tracking nodes to mark reachable when
  /// walking over the CFG in `fixedpoint_to_assertions` and
  /// `fixedpoint_from_assertions`.
  struct search_stack_entryt
  {
    /// CFG node to mark reachable
    cfgt::node_indext node_index;

    /// If true, this function's caller is known and has already been queued to
    /// mark reachable, so there is no need to queue anything when walking out
    /// of the function, whether forwards (via END_FUNCTION) or backwards (via a
    /// callsite).
    /// If false, this function's caller is not known, so when walking forwards
    /// from the end or backwards from the beginning we should queue all
    /// possible callers.
    bool caller_is_known;

    search_stack_entryt(cfgt::node_indext node_index, bool caller_is_known) :
      node_index(node_index), caller_is_known(caller_is_known)
    {
    }
  };

  void fixedpoint_to_assertions(
    const is_threadedt &is_threaded,
    slicing_criteriont &criterion);

  void fixedpoint_from_assertions(
    const is_threadedt &is_threaded,
    slicing_criteriont &criterion);

  void slice(goto_functionst &goto_functions);

private:
  std::vector<cfgt::node_indext>
  get_sources(const is_threadedt &is_threaded, slicing_criteriont &criterion);
};

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H
