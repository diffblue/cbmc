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
/// \param is_threaded Instructions that might be executed concurrently
/// \param criterion The criterion we care about
std::vector<reachability_slicert::cfgt::node_indext>
reachability_slicert::get_sources(
  const is_threadedt &is_threaded,
  slicing_criteriont &criterion)
{
  std::vector<cfgt::node_indext> sources;
  for(const auto &e_it : cfg.entry_map)
  {
    if(criterion(e_it.first) || is_threaded(e_it.first))
      sources.push_back(e_it.second);
  }

  return sources;
}

static bool is_same_target(
  goto_programt::const_targett it1,
  goto_programt::const_targett it2)
{
  // Avoid comparing iterators belonging to different functions, and therefore
  // different std::lists.
  return it1->function == it2->function && it1 == it2;
}

/// Perform backwards depth-first search of the control-flow graph of the
/// goto program, starting from the nodes corresponding to the criterion and
/// the instructions that might be executed concurrently. Set reaches_assertion
/// to true for every instruction visited.
/// \param is_threaded Instructions that might be executed concurrently
/// \param criterion the criterion we are trying to hit
void reachability_slicert::fixedpoint_to_assertions(
  const is_threadedt &is_threaded,
  slicing_criteriont &criterion)
{
  std::vector<search_stack_entryt> stack;
  std::vector<cfgt::node_indext> sources = get_sources(is_threaded, criterion);
  for(const auto source : sources)
    stack.emplace_back(source, false);

  while(!stack.empty())
  {
    auto &node = cfg[stack.back().node_index];
    const auto caller_is_known = stack.back().caller_is_known;
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
        // Queue both the caller and the end of the callee.
        INVARIANT(
          std::prev(node.PC)->is_function_call(),
          "all function return edges should point to the successor of a "
          "FUNCTION_CALL instruction");
        stack.emplace_back(edge.first, true);
        stack.emplace_back(cfg.entry_map[std::prev(node.PC)], caller_is_known);
      }
      else if(pred_node.PC->is_function_call())
      {
        // Skip this predecessor, unless this is a bodyless function, or we
        // don't know who our callee was:
        if(!caller_is_known || is_same_target(std::next(pred_node.PC), node.PC))
          stack.emplace_back(edge.first, caller_is_known);
      }
      else
      {
        stack.emplace_back(edge.first, caller_is_known);
      }
    }
  }
}

/// Perform forwards depth-first search of the control-flow graph of the
/// goto program, starting from the nodes corresponding to the criterion and
/// the instructions that might be executed concurrently. Set reaches_assertion
/// to true for every instruction visited.
/// \param is_threaded Instructions that might be executed concurrently
/// \param criterion the criterion we are trying to hit
void reachability_slicert::fixedpoint_from_assertions(
  const is_threadedt &is_threaded,
  slicing_criteriont &criterion)
{
  std::vector<search_stack_entryt> stack;
  std::vector<cfgt::node_indext> sources = get_sources(is_threaded, criterion);
  for(const auto source : sources)
    stack.emplace_back(source, false);

  while(!stack.empty())
  {
    auto &node = cfg[stack.back().node_index];
    const auto caller_is_known = stack.back().caller_is_known;
    stack.pop_back();

    if(node.reachable_from_assertion)
      continue;
    node.reachable_from_assertion = true;

    if(node.PC->is_function_call())
    {
      // Queue the instruction's natural successor (function head, or next
      // instruction if the function is bodyless)
      INVARIANT(node.out.size() == 1, "Call sites should have one successor");
      const auto successor_index = node.out.begin()->first;

      // If the function has a body, mark the function head, but note that we
      // have already taken care of the return site.
      const auto &callee_head_node = cfg[successor_index];
      auto callee_it = callee_head_node.PC;
      if(!is_same_target(callee_it, std::next(node.PC)))
      {
        stack.emplace_back(successor_index, true);

        // Check if it can return, and if so mark the callsite's successor:
        while(!callee_it->is_end_function())
          ++callee_it;

        if(!cfg[cfg.entry_map[callee_it]].out.empty())
        {
          stack.emplace_back(
            cfg.entry_map[std::next(node.PC)], caller_is_known);
        }
      }
      else
      {
        // Bodyless function -- mark the successor instruction only.
        stack.emplace_back(successor_index, caller_is_known);
      }
    }
    else if(node.PC->is_end_function() && caller_is_known)
    {
      // Special case -- the callsite successor was already queued when entering
      // this function, more precisely than we can see from the function return
      // edges (which lead to all possible callers), so nothing to do here.
    }
    else
    {
      // General case, including end-of-function where we don't know our caller.
      // Queue all successors.
      for(const auto &edge : node.out)
        stack.emplace_back(edge.first, caller_is_known);
    }
  }
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
/// \param goto_model Goto program to slice
/// \param include_forward_reachability Determines if only instructions
/// from which the criterion is reachable should be kept (false) or also
/// those reachable from the criterion (true)
void reachability_slicer(
  goto_modelt &goto_model,
  const bool include_forward_reachability)
{
  reachability_slicert s;
  assert_criteriont a;
  s(goto_model.goto_functions, a, include_forward_reachability);
}

/// Perform reachability slicing on goto_model for selected properties.
/// \param goto_model Goto program to slice
/// \param properties The properties relevant for the slicing (i.e. starting
/// point for the search in the cfg)
/// \param include_forward_reachability Determines if only instructions
/// from which the criterion is reachable should be kept (false) or also
/// those reachable from the criterion (true)
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
/// \param goto_model Goto program to slice
/// \param functions_list The functions relevant for the slicing (i.e. starting
/// point for the search in the CFG). Anything that is reachable in the CFG
/// starting from these functions will be kept.
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
/// \param goto_model Goto program to slice
void reachability_slicer(goto_modelt &goto_model)
{
  reachability_slicer(goto_model, false);
}

/// Perform reachability slicing on goto_model for selected properties. Only
/// instructions from which the criterion is reachable will be kept.
/// \param goto_model Goto program to slice
/// \param properties The properties relevant for the slicing (i.e. starting
/// point for the search in the cfg)
void reachability_slicer(
  goto_modelt &goto_model,
  const std::list<std::string> &properties)
{
  reachability_slicer(goto_model, properties, false);
}
