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
    const slicing_criteriont &criterion,
    bool include_forward_reachability)
  {
    cfg(goto_functions);
    forall_goto_functions(f_it, goto_functions)
    {
      forall_goto_program_instructions(i_it, f_it->second.body)
        cfg[cfg.entry_map[i_it]].function_id = f_it->first;
    }

    is_threadedt is_threaded(goto_functions);
    fixedpoint_to_assertions(is_threaded, criterion);
    if(include_forward_reachability)
      fixedpoint_from_assertions(is_threaded, criterion);
    slice(goto_functions);
  }

protected:
  struct slicer_entryt
  {
    slicer_entryt() : reaches_assertion(false), reachable_from_assertion(false)
    {
    }

    irep_idt function_id;
    bool reaches_assertion;
    bool reachable_from_assertion;
  };

  bool is_same_target(
    goto_programt::const_targett it1,
    goto_programt::const_targett it2) const;

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
    const slicing_criteriont &criterion);

  void fixedpoint_from_assertions(
    const is_threadedt &is_threaded,
    const slicing_criteriont &criterion);

  void slice(goto_functionst &goto_functions);

private:
  std::vector<cfgt::node_indext>
    backward_outwards_walk_from(std::vector<cfgt::node_indext>);

  void backward_inwards_walk_from(std::vector<cfgt::node_indext>);

  std::vector<cfgt::node_indext>
    forward_outwards_walk_from(std::vector<cfgt::node_indext>);

  void forward_inwards_walk_from(std::vector<cfgt::node_indext>);

  void forward_walk_call_instruction(
    const cfgt::nodet &call_node,
    std::vector<cfgt::node_indext> &callsite_successor_stack,
    std::vector<cfgt::node_indext> &callee_head_stack);

  std::vector<cfgt::node_indext> get_sources(
    const is_threadedt &is_threaded,
    const slicing_criteriont &criterion);
};

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H
