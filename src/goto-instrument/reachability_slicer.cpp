/*******************************************************************\

Module: Slicer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Reachability Slicer
/// Consider the control flow graph of the goto program and a criterion, and
/// remove the parts of the graph from which the criterion is not reachable
/// (and possibly, depending on the parameters, keep those that can be reached
/// from the criterion).

#include "reachability_slicer.h"

#include <stack>

#include <goto-programs/cfg.h>
#include <goto-programs/remove_calls_no_body.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>

#include "util/message.h"

#include "full_slicer_class.h"
#include "reachability_slicer_class.h"

/// Get the set of nodes that correspond to the given criterion, or that can
/// appear in concurrent execution. None of these should be sliced away so
/// they are used as a basis for the search.
/// \param is_threaded: Instructions that might be executed concurrently
/// \param criterion: The criterion we care about
std::vector<reachability_slicert::cfgt::node_indext>
reachability_slicert::get_sources(
  const is_threadedt &is_threaded,
  const slicing_criteriont &criterion)
{
  std::vector<cfgt::node_indext> sources;
  for(const auto &e_it : cfg.entry_map)
  {
    if(
      criterion(cfg[e_it.second].function_id, e_it.first) ||
      is_threaded(e_it.first))
      sources.push_back(e_it.second);
  }

  return sources;
}

bool reachability_slicert::is_same_target(
  goto_programt::const_targett it1,
  goto_programt::const_targett it2) const
{
  // Avoid comparing iterators belonging to different functions, and therefore
  // different std::lists.
  cfgt::entry_mapt::const_iterator it1_entry = cfg.entry_map.find(it1);
  cfgt::entry_mapt::const_iterator it2_entry = cfg.entry_map.find(it2);
  return it1_entry != cfg.entry_map.end() && it2_entry != cfg.entry_map.end() &&
         cfg[it1_entry->second].function_id ==
           cfg[it2_entry->second].function_id &&
         it1 == it2;
}

/// Perform backward depth-first search of the control-flow graph of the
/// goto program, starting from a given set of nodes. At call sites this walks
/// to all possible callers, and at return sites it remembers the site but
/// doesn't walk in (this will be done in `backward_inwards_walk_from` below).
/// \param stack: nodes to start from
/// \return vector of return-site nodes encountered during the walk
std::vector<reachability_slicert::cfgt::node_indext>
reachability_slicert::backward_outwards_walk_from(
  std::vector<cfgt::node_indext> stack)
{
  std::vector<cfgt::node_indext> return_sites;

  while(!stack.empty())
  {
    auto &node = cfg[stack.back()];
    stack.pop_back();

    if(node.reaches_assertion)
      continue;
    node.reaches_assertion = true;

    for(const auto &edge : node.in)
    {
      const auto &pred_node = cfg[edge.first];

      if(pred_node.PC->is_end_function())
      {
        // This is an end-of-function -> successor-of-callsite edge.
        // Record the return site for later investigation and step over it:
        return_sites.push_back(edge.first);

        INVARIANT(
          std::prev(node.PC)->is_function_call(),
          "all function return edges should point to the successor of a "
          "FUNCTION_CALL instruction");

        stack.push_back(cfg.entry_map[std::prev(node.PC)]);
      }
      else
      {
        stack.push_back(edge.first);
      }
    }
  }

  return return_sites;
}

/// Perform backward depth-first search of the control-flow graph of the
/// goto program, starting from a given set of nodes. This walks into return
/// sites but *not* out of call sites; this is the opposite of
/// `backward_outwards_walk_from` above. Note since the two functions use the
/// same `reaches_assertion` flag to track where they have been, it is important
/// the outwards walk is performed before the inwards walk, as encountering a
/// function while walking outwards visits strictly more code than when walking
/// inwards.
/// \param stack: nodes to start from
void reachability_slicert::backward_inwards_walk_from(
  std::vector<cfgt::node_indext> stack)
{
  while(!stack.empty())
  {
    auto &node = cfg[stack.back()];
    stack.pop_back();

    if(node.reaches_assertion)
      continue;
    node.reaches_assertion = true;

    for(const auto &edge : node.in)
    {
      const auto &pred_node = cfg[edge.first];

      if(pred_node.PC->is_end_function())
      {
        // This is an end-of-function -> successor-of-callsite edge.
        // Walk into the called function, and then walk from the callsite
        // backward:
        stack.push_back(edge.first);

        INVARIANT(
          std::prev(node.PC)->is_function_call(),
          "all function return edges should point to the successor of a "
          "FUNCTION_CALL instruction");

        stack.push_back(cfg.entry_map[std::prev(node.PC)]);
      }
      else if(pred_node.PC->is_function_call())
      {
        // Skip -- the callsite relevant to this function was already queued
        // when we processed the return site.
      }
      else
      {
        stack.push_back(edge.first);
      }
    }
  }
}

/// Perform backward depth-first search of the control-flow graph of the
/// goto program, starting from the nodes corresponding to the criterion and
/// the instructions that might be executed concurrently. Set reaches_assertion
/// to true for every instruction visited.
/// \param is_threaded: Instructions that might be executed concurrently
/// \param criterion: the criterion we are trying to hit
void reachability_slicert::fixedpoint_to_assertions(
  const is_threadedt &is_threaded,
  const slicing_criteriont &criterion)
{
  std::vector<cfgt::node_indext> sources = get_sources(is_threaded, criterion);

  // First walk outwards towards __CPROVER_start, visiting all possible callers
  // and stepping over but recording callees as we go:
  std::vector<cfgt::node_indext> return_sites =
    backward_outwards_walk_from(sources);

  // Now walk into those callees, restricting our walk to the known callsites:
  backward_inwards_walk_from(return_sites);
}

/// Process a call instruction during a forwards reachability walk.
/// \param call_node: function-call graph node. Its single successor will be
///   the head of the callee if the callee body exists, or the call
///   instruction's immediate successor otherwise.
/// \param callsite_successor_stack: The index of the callsite's local successor
///   node will be added to this vector if it is reachable.
/// \param callee_head_stack: The index of the callee body head node will be
///   added to this vector if the callee has a body.
void reachability_slicert::forward_walk_call_instruction(
  const cfgt::nodet &call_node,
  std::vector<cfgt::node_indext> &callsite_successor_stack,
  std::vector<cfgt::node_indext> &callee_head_stack)
{
  // Get the instruction's natural successor (function head, or next
  // instruction if the function is bodyless)
  INVARIANT(call_node.out.size() == 1, "Call sites should have one successor");
  const auto successor_index = call_node.out.begin()->first;

  auto callsite_successor_pc = std::next(call_node.PC);

  auto successor_pc = cfg[successor_index].PC;
  if(!is_same_target(successor_pc, callsite_successor_pc))
  {
    // Real call -- store the callee head node:
    callee_head_stack.push_back(successor_index);

    // Check if it can return, and if so store the callsite's successor:
    while(!successor_pc->is_end_function())
      ++successor_pc;

    if(!cfg[cfg.entry_map[successor_pc]].out.empty())
      callsite_successor_stack.push_back(cfg.entry_map[callsite_successor_pc]);
  }
  else
  {
    // Bodyless function -- mark the successor instruction only.
    callsite_successor_stack.push_back(successor_index);
  }
}

/// Perform forwards depth-first search of the control-flow graph of the
/// goto program, starting from a given set of nodes. Steps over and records
/// callsites for a later inwards walk; explores all possible callers at return
/// sites, eventually walking out into __CPROVER__start.
/// \param stack: nodes to start from
/// \return vector of encounted callee head nodes
std::vector<reachability_slicert::cfgt::node_indext>
reachability_slicert::forward_outwards_walk_from(
  std::vector<cfgt::node_indext> stack)
{
  std::vector<cfgt::node_indext> called_function_heads;

  while(!stack.empty())
  {
    auto &node = cfg[stack.back()];
    stack.pop_back();

    if(node.reachable_from_assertion)
      continue;
    node.reachable_from_assertion = true;

    if(node.PC->is_function_call())
    {
      // Store the called function head for the later inwards walk;
      // visit the call instruction's local successor now.
      forward_walk_call_instruction(node, stack, called_function_heads);
    }
    else
    {
      // General case, including end of function: queue all successors.
      for(const auto &edge : node.out)
        stack.push_back(edge.first);
    }
  }

  return called_function_heads;
}

/// Perform forwards depth-first search of the control-flow graph of the
/// goto program, starting from a given set of nodes. Steps into callsites;
/// ignores return sites, which have been taken care of by
/// `forward_outwards_walk_from`. Note it is important this is done *after*
/// the outwards walk, because the outwards walk visits strictly more functions
/// as it visits all possible callers.
/// \param stack: nodes to start from
void reachability_slicert::forward_inwards_walk_from(
  std::vector<cfgt::node_indext> stack)
{
  while(!stack.empty())
  {
    auto &node = cfg[stack.back()];
    stack.pop_back();

    if(node.reachable_from_assertion)
      continue;
    node.reachable_from_assertion = true;

    if(node.PC->is_function_call())
    {
      // Visit both the called function head and the callsite successor:
      forward_walk_call_instruction(node, stack, stack);
    }
    else if(node.PC->is_end_function())
    {
      // Special case -- the callsite successor was already queued when entering
      // this function, more precisely than we can see from the function return
      // edges (which lead to all possible callers), so nothing to do here.
    }
    else
    {
      // General case: queue all successors.
      for(const auto &edge : node.out)
        stack.push_back(edge.first);
    }
  }
}

/// Perform forwards depth-first search of the control-flow graph of the
/// goto program, starting from the nodes corresponding to the criterion and
/// the instructions that might be executed concurrently. Set reaches_assertion
/// to true for every instruction visited.
/// \param is_threaded: Instructions that might be executed concurrently
/// \param criterion: the criterion we are trying to hit
void reachability_slicert::fixedpoint_from_assertions(
  const is_threadedt &is_threaded,
  const slicing_criteriont &criterion)
{
  std::vector<cfgt::node_indext> sources = get_sources(is_threaded, criterion);

  // First walk outwards towards __CPROVER_start, visiting all possible callers
  // and stepping over but recording callees as we go:
  std::vector<cfgt::node_indext> return_sites =
    forward_outwards_walk_from(sources);

  // Now walk into those callees, restricting our walk to the known callsites:
  forward_inwards_walk_from(return_sites);
}

/// This function removes all instructions that have the flag
/// reaches_assertion or reachable_from_assertion set to true;
void reachability_slicert::slice(goto_functionst &goto_functions)
{
  // now replace those instructions that do not reach any assertions
  // by assume(false)

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available())
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        cfgt::nodet &e = cfg[cfg.entry_map[i_it]];
        if(
          !e.reaches_assertion && !e.reachable_from_assertion &&
          !i_it->is_end_function())
          i_it->make_assumption(false_exprt());
      }

      // replace unreachable code by skip
      remove_unreachable(f_it->second.body);
    }

  // remove the skips
  remove_skip(goto_functions);
}

/// Perform reachability slicing on goto_model, with respect to the
/// criterion given by all properties.
/// \param goto_model: Goto program to slice
/// \param include_forward_reachability: Determines if only instructions
///   from which the criterion is reachable should be kept (false) or also
///   those reachable from the criterion (true)
void reachability_slicer(
  goto_modelt &goto_model,
  const bool include_forward_reachability)
{
  reachability_slicert s;
  assert_criteriont a;
  s(goto_model.goto_functions, a, include_forward_reachability);
}

/// Perform reachability slicing on goto_model for selected properties.
/// \param goto_model: Goto program to slice
/// \param properties: The properties relevant for the slicing (i.e. starting
///   point for the search in the cfg)
/// \param include_forward_reachability: Determines if only instructions
///   from which the criterion is reachable should be kept (false) or also
///   those reachable from the criterion (true)
void reachability_slicer(
  goto_modelt &goto_model,
  const std::list<std::string> &properties,
  const bool include_forward_reachability)
{
  reachability_slicert s;
  properties_criteriont p(properties);
  s(goto_model.goto_functions, p, include_forward_reachability);
}

/// Perform reachability slicing on goto_model for selected functions.
/// \param goto_model: Goto program to slice
/// \param functions_list: The functions relevant for the slicing (i.e. starting
///   point for the search in the CFG). Anything that is reachable in the CFG
///   starting from these functions will be kept.
void function_path_reachability_slicer(
  goto_modelt &goto_model,
  const std::list<std::string> &functions_list)
{
  for(const auto &function : functions_list)
  {
    in_function_criteriont matching_criterion(function);
    reachability_slicert slicer;
    slicer(goto_model.goto_functions, matching_criterion, true);
  }

  remove_calls_no_bodyt remove_calls_no_body;
  remove_calls_no_body(goto_model.goto_functions);

  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();
}

/// Perform reachability slicing on goto_model, with respect to criterion
/// comprising all properties. Only instructions from which the criterion
/// is reachable will be kept.
/// \param goto_model: Goto program to slice
void reachability_slicer(goto_modelt &goto_model)
{
  reachability_slicer(goto_model, false);
}

/// Perform reachability slicing on goto_model for selected properties. Only
/// instructions from which the criterion is reachable will be kept.
/// \param goto_model: Goto program to slice
/// \param properties: The properties relevant for the slicing (i.e. starting
///   point for the search in the cfg)
void reachability_slicer(
  goto_modelt &goto_model,
  const std::list<std::string> &properties)
{
  reachability_slicer(goto_model, properties, false);
}
