/*******************************************************************\

Module: Remove initializations of unused global variables

Author: Daniel Poetzl

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove initializations of unused global variables

#include "slice_global_inits.h"

#include <util/cprover_prefix.h>
#include <util/find_symbols.h>
#include <util/std_expr.h>

#include <analyses/call_graph.h>
#include <linking/static_lifetime_init.h>

#include "goto_functions.h"
#include "goto_model.h"

#include <algorithm>
#include <map>
#include <unordered_set>
#include <vector>

void slice_global_inits(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  // gather all functions reachable from the entry point
  const irep_idt entry_point=goto_functionst::entry_point();
  goto_functionst &goto_functions=goto_model.goto_functions;

  if(goto_functions.function_map.count(entry_point) == 0)
    throw user_input_error_exceptiont("entry point not found");

  // Get the call graph restricted to functions reachable from
  // the entry point:
  call_grapht call_graph =
    call_grapht::create_from_root_function(goto_model, entry_point, false);
  const auto directed_graph = call_graph.get_directed_graph();
  INVARIANT(
    !directed_graph.empty(),
    "at least " + id2string(entry_point) + " should be reachable");

  // gather all symbols used by reachable functions

  find_symbols_sett symbols_to_keep;

  for(std::size_t node_idx = 0; node_idx < directed_graph.size(); ++node_idx)
  {
    const irep_idt &id = directed_graph[node_idx].function;
    if(id == INITIALIZE_FUNCTION)
      continue;

    // assume function has no body if it is not in the function map
    const auto &it = goto_functions.function_map.find(id);
    if(it == goto_functions.function_map.end())
      continue;

    for(const auto &i : it->second.body.instructions)
    {
      i.apply([&symbols_to_keep](const exprt &expr) {
        find_symbols(expr, symbols_to_keep);
      });
    }
  }

  goto_functionst::function_mapt::iterator f_it;
  f_it=goto_functions.function_map.find(INITIALIZE_FUNCTION);

  if(f_it == goto_functions.function_map.end())
    throw incorrect_goto_program_exceptiont("initialize function not found");

  goto_programt &goto_program=f_it->second.body;

  // add all symbols from right-hand sides of required symbols
  bool fixed_point_reached = false;
  // markers for each instruction to avoid repeatedly searching the same
  // instruction for new symbols; initialized to false, and set to true whenever
  // an instruction is determined to be irrelevant (not an assignment) or
  // symbols have been collected from it
  std::vector<bool> seen(goto_program.instructions.size(), false);
  while(!fixed_point_reached)
  {
    fixed_point_reached = true;

    std::vector<bool>::iterator seen_it = seen.begin();
    for(const auto &instruction : goto_program.instructions)
    {
      if(!*seen_it && instruction.is_assign())
      {
        const irep_idt id =
          to_symbol_expr(instruction.assign_lhs()).identifier();

        // if we are to keep the left-hand side, then we also need to keep all
        // symbols occurring in the right-hand side
        if(
          id.starts_with(CPROVER_PREFIX) ||
          symbols_to_keep.find(id) != symbols_to_keep.end())
        {
          fixed_point_reached = false;
          find_symbols(instruction.assign_rhs(), symbols_to_keep);
          *seen_it = true;
        }
      }
      else if(!*seen_it)
        *seen_it = true;

      ++seen_it;
    }
  }

  // now remove unnecessary initializations
  bool changed = false;
  for(auto it = goto_model.symbol_table.begin();
      it != goto_model.symbol_table.end();
      ++it)
  {
    if(
      it->second.is_static_lifetime && !it->second.is_type &&
      !it->second.is_macro && it->second.type.id() != ID_code &&
      !it->first.starts_with(CPROVER_PREFIX) &&
      symbols_to_keep.find(it->first) == symbols_to_keep.end())
    {
      symbolt &symbol = it.get_writeable_symbol();
      symbol.is_extern = true;
      symbol.value.make_nil();
      symbol.value.set(ID_C_no_nondet_initialization, 1);
      changed = true;
    }
  }

  if(changed && goto_model.can_produce_function(INITIALIZE_FUNCTION))
    recreate_initialize_function(goto_model, message_handler);
}

void slice_unused_virtual_tables(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  goto_functionst &goto_functions = goto_model.goto_functions;
  const auto initialize = goto_functions.function_map.find(INITIALIZE_FUNCTION);
  if(
    goto_functions.function_map.count(goto_functionst::entry_point()) == 0 ||
    initialize == goto_functions.function_map.end())
  {
    return;
  }

  const auto is_virtual_table = [](const irep_idt &id)
  { return id.starts_with("virtual_table::"); };
  if(std::none_of(
       goto_model.symbol_table.begin(),
       goto_model.symbol_table.end(),
       [&](const auto &entry) { return is_virtual_table(entry.first); }))
  {
    return;
  }

  // The initialization function's assignments are followed only for the
  // globals that are kept; its other instructions (the calls of dynamic
  // initialization functions) are followed as those of any function.
  std::multimap<irep_idt, const exprt *> initializers;
  std::vector<const exprt *> initialize_other;
  for(const auto &instruction : initialize->second.body.instructions)
  {
    if(instruction.is_assign() && instruction.assign_lhs().id() == ID_symbol)
    {
      initializers.emplace(
        to_symbol_expr(instruction.assign_lhs()).get_identifier(),
        &instruction.assign_rhs());
    }
    else
    {
      // apply() does not visit the callee of a function call
      if(instruction.is_function_call())
        initialize_other.push_back(&instruction.call_function());
      instruction.apply([&initialize_other](const exprt &expr)
                        { initialize_other.push_back(&expr); });
    }
  }

  std::unordered_set<irep_idt> kept;
  std::vector<irep_idt> work;
  const auto keep_symbols_of = [&](const exprt &expr)
  {
    find_symbols_sett found;
    find_symbols(expr, found);
    for(const irep_idt &id : found)
      if(kept.insert(id).second)
        work.push_back(id);
  };

  // Functions are reachable when named in reachable code: called directly,
  // or with their address taken (possibly called through it later).
  kept.insert(goto_functionst::entry_point());
  work.push_back(goto_functionst::entry_point());
  kept.insert(INITIALIZE_FUNCTION);
  for(const exprt *expr : initialize_other)
    keep_symbols_of(*expr);
  while(!work.empty())
  {
    const irep_idt id = work.back();
    work.pop_back();
    const auto range = initializers.equal_range(id);
    for(auto it = range.first; it != range.second; ++it)
      keep_symbols_of(*it->second);
    const auto function = goto_functions.function_map.find(id);
    if(
      function == goto_functions.function_map.end() ||
      id == INITIALIZE_FUNCTION)
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(instruction.is_function_call())
        keep_symbols_of(instruction.call_function());
      instruction.apply(keep_symbols_of);
    }
  }

  bool changed = false;
  for(auto it = goto_model.symbol_table.begin();
      it != goto_model.symbol_table.end();
      ++it)
  {
    if(
      is_virtual_table(it->first) && it->second.is_static_lifetime &&
      kept.count(it->first) == 0 && it->second.value.is_not_nil())
    {
      symbolt &symbol = it.get_writeable_symbol();
      symbol.is_extern = true;
      symbol.value.make_nil();
      symbol.value.set(ID_C_no_nondet_initialization, 1);
      changed = true;
    }
  }

  if(changed && goto_model.can_produce_function(INITIALIZE_FUNCTION))
    recreate_initialize_function(goto_model, message_handler);
}
