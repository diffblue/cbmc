/*******************************************************************\

Module: Fatal Assertions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Fatal Assertions

#include "fatal_assertions.h"

#include <util/irep_hash.h>

#include <goto-programs/goto_functions.h>

#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct function_loc_pairt
{
  using function_itt = goto_functionst::function_mapt::const_iterator;
  function_loc_pairt(
    function_itt __function_it,
    goto_programt::const_targett __target)
    : function_it(__function_it), target(__target)
  {
  }
  function_itt function_it;
  goto_programt::const_targett target;
  bool operator==(const function_loc_pairt &other) const
  {
    return function_it->first == other.function_it->first &&
           target == other.target;
  }
};

struct function_itt_hasht
{
  using function_itt = goto_functionst::function_mapt::const_iterator;
  std::size_t operator()(const function_itt &function_it) const
  {
    return function_it->first.hash();
  }
};

struct function_loc_pair_hasht
{
  std::size_t operator()(const function_loc_pairt &p) const
  {
    auto h1 = p.function_it->first.hash();
    auto h2 = const_target_hash{}(p.target);
    return hash_combine(h1, h2);
  }
};

using loc_sett =
  std::unordered_set<function_loc_pairt, function_loc_pair_hasht>;

/// The call sites of each function that is called directly.
static std::unordered_map<irep_idt, std::vector<function_loc_pairt>>
call_sites(const goto_functionst &goto_functions)
{
  std::unordered_map<irep_idt, std::vector<function_loc_pairt>> result;

  for(auto function_it = goto_functions.function_map.begin();
      function_it != goto_functions.function_map.end();
      function_it++)
  {
    auto &body = function_it->second.body;
    for(auto target = body.instructions.begin();
        target != body.instructions.end();
        target++)
    {
      if(
        target->is_function_call() && target->call_function().id() == ID_symbol)
      {
        result[to_symbol_expr(target->call_function()).get_identifier()]
          .emplace_back(function_it, target);
      }
    }
  }

  return result;
}

/// All locations that may execute after any of \p locs: their successors,
/// the bodies of the functions they call, and, when the end of the function
/// holding one of \p locs is reached, the continuations of all its call sites
/// (and so on transitively). A callee entered through a call returns to that
/// call only, whose continuation is added at the call.
static loc_sett
reachable_fixpoint(const loc_sett &locs, const goto_functionst &goto_functions)
{
  const auto callers = call_sites(goto_functions);

  // frontier set, with whether the calling context is unknown: if it is, the
  // end of the function returns to any of its call sites
  std::stack<std::pair<function_loc_pairt, bool>> working;

  for(auto loc : locs)
    working.emplace(loc, true);

  loc_sett fixpoint;
  loc_sett any_caller;

  while(!working.empty())
  {
    auto loc = working.top().first;
    const bool unknown_context = working.top().second;
    working.pop();

    bool seen = !fixpoint.insert(loc).second;
    if(unknown_context)
      seen = !any_caller.insert(loc).second;
    if(seen)
      continue;

    if(loc.target->is_function_call())
    {
      // get the callee
      auto &function = loc.target->call_function();
      if(function.id() == ID_symbol)
      {
        // add the callee to the working set
        auto &function_identifier = to_symbol_expr(function).identifier();
        auto function_iterator =
          goto_functions.function_map.find(function_identifier);
        CHECK_RETURN(function_iterator != goto_functions.function_map.end());
        if(!function_iterator->second.body.instructions.empty())
        {
          working.emplace(
            function_loc_pairt{
              function_iterator,
              function_iterator->second.body.instructions.begin()},
            false);
        }
      }

      // add the next location to the working set
      working.emplace(
        function_loc_pairt{loc.function_it, std::next(loc.target)},
        unknown_context);
    }
    else if(loc.target->is_end_function())
    {
      // with an unknown calling context, execution continues after any call
      // site of this function
      auto callers_it = callers.find(loc.function_it->first);
      if(unknown_context && callers_it != callers.end())
      {
        for(const auto &call_site : callers_it->second)
        {
          working.emplace(
            function_loc_pairt{
              call_site.function_it, std::next(call_site.target)},
            true);
        }
      }
    }
    else
    {
      auto &body = loc.function_it->second.body;

      for(auto successor : body.get_successors(loc.target))
      {
        working.emplace(
          function_loc_pairt{loc.function_it, successor}, unknown_context);
      }
    }
  }

  return fixpoint;
}

/// Proven assertions after refuted fatal assertions
/// are marked as UNKNOWN.
///
/// In a multi-threaded program, code that does not follow a refuted fatal
/// assertion in the control-flow graph can still run after it: the code of
/// other threads. Any such code is reachable from some START_THREAD
/// instruction, because at least two threads exist at that point. We then
/// also start from every START_THREAD instruction.
void propagate_fatal_to_proven(
  propertiest &properties,
  const goto_functionst &goto_functions)
{
  // Iterate to find refuted fatal assertions. Anything reachalble
  // from there is a 'fatal loc'.
  loc_sett fatal_locs;
  loc_sett thread_starts;

  for(auto function_it = goto_functions.function_map.begin();
      function_it != goto_functions.function_map.end();
      function_it++)
  {
    auto &body = function_it->second.body;
    for(auto target = body.instructions.begin();
        target != body.instructions.end();
        target++)
    {
      if(target->is_assert() && target->source_location().property_fatal())
      {
        auto id = target->source_location().get_property_id();
        auto property = properties.find(id);
        CHECK_RETURN(property != properties.end());

        // Status?
        if(property->second.status == property_statust::FAIL)
        {
          fatal_locs.emplace(function_it, target);
        }
      }
      else if(target->is_start_thread())
        thread_starts.emplace(function_it, target);
    }
  }

  if(!fatal_locs.empty())
    fatal_locs.insert(thread_starts.begin(), thread_starts.end());

  // Saturate fixpoint.
  auto fixpoint = reachable_fixpoint(fatal_locs, goto_functions);

  // Now mark PASS assertions as UNKNOWN.
  for(auto &loc : fixpoint)
  {
    if(loc.target->is_assert())
    {
      auto id = loc.target->source_location().get_property_id();
      auto property = properties.find(id);
      CHECK_RETURN(property != properties.end());

      // Status?
      if(property->second.status == property_statust::PASS)
      {
        property->second.status = property_statust::UNKNOWN;
      }
    }
  }
}

void propagate_fatal_assertions(
  propertiest &properties,
  const goto_functionst &goto_functions)
{
  propagate_fatal_to_proven(properties, goto_functions);
}
