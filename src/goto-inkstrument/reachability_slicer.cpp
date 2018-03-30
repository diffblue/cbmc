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

#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>
#include <goto-programs/cfg.h>

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
  std::vector<cfgt::node_indext> src = get_sources(is_threaded, criterion);

  std::vector<cfgt::node_indext> reachable = cfg.get_reachable(src, false);
  for(const auto index : reachable)
    cfg[index].reaches_assertion = true;
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
  std::vector<cfgt::node_indext> src = get_sources(is_threaded, criterion);

  const std::vector<cfgt::node_indext> reachable = cfg.get_reachable(src, true);
  for(const auto index : reachable)
    cfg[index].reachable_from_assertion = true;
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
        const cfgt::nodet &e=cfg[cfg.entry_map[i_it]];
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
  goto_functions.update();
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
