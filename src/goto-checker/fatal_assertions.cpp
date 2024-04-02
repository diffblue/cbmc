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
#include <unordered_set>

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

static loc_sett
reachable_fixpoint(const loc_sett &locs, const goto_functionst &goto_functions)
{
  // frontier set
  std::stack<function_loc_pairt> working;

  for(auto loc : locs)
    working.push(loc);

  loc_sett fixpoint;

  while(!working.empty())
  {
    auto loc = working.top();
    working.pop();

    auto insertion_result = fixpoint.insert(loc);
    if(!insertion_result.second)
      continue; // seen already

    if(loc.target->is_function_call())
    {
      // get the callee
      auto &function = loc.target->call_function();
      if(function.id() == ID_symbol)
      {
        // add the callee to the working set
        auto &function_identifier = to_symbol_expr(function).get_identifier();
        auto function_iterator =
          goto_functions.function_map.find(function_identifier);
        CHECK_RETURN(function_iterator != goto_functions.function_map.end());
        working.emplace(
          function_iterator,
          function_iterator->second.body.instructions.begin());
      }

      // add the next location to the working set
      working.emplace(loc.function_it, std::next(loc.target));
    }
    else
    {
      auto &body = loc.function_it->second.body;

      for(auto successor : body.get_successors(loc.target))
        working.emplace(loc.function_it, successor);
    }
  }

  return fixpoint;
}

/// Proven assertions after refuted fatal assertions
/// are marked as UNKNOWN.
void propagate_fatal_to_proven(
  propertiest &properties,
  const goto_functionst &goto_functions)
{
  // Iterate to find refuted fatal assertions. Anything reachalble
  // from there is a 'fatal loc'.
  loc_sett fatal_locs;

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
    }
  }

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
