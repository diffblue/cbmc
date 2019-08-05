/*******************************************************************\

Module: Remove initializations of unused global variables

Author: Daniel Poetzl

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove initializations of unused global variables

#include "slice_global_inits.h"

#include <analyses/call_graph.h>

#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <util/invariant.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_skip.h>

#include <linking/static_lifetime_init.h>

void slice_global_inits(goto_modelt &goto_model)
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
        find_symbols(expr, symbols_to_keep, true, false);
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
    forall_goto_program_instructions(i_it, goto_program)
    {
      if(!*seen_it && i_it->is_assign())
      {
        const code_assignt &code_assign = i_it->get_assign();
        const irep_idt id = to_symbol_expr(code_assign.lhs()).get_identifier();

        // if we are to keep the left-hand side, then we also need to keep all
        // symbols occurring in the right-hand side
        if(
          has_prefix(id2string(id), CPROVER_PREFIX) ||
          symbols_to_keep.find(id) != symbols_to_keep.end())
        {
          fixed_point_reached = false;
          find_symbols(code_assign.rhs(), symbols_to_keep, true, false);
          *seen_it = true;
        }
      }
      else if(!*seen_it)
        *seen_it = true;

      ++seen_it;
    }
  }

  // now remove unnecessary initializations
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_assign())
    {
      const code_assignt &code_assign = i_it->get_assign();
      const symbol_exprt &symbol_expr=to_symbol_expr(code_assign.lhs());
      const irep_idt id=symbol_expr.get_identifier();

      if(
        !has_prefix(id2string(id), CPROVER_PREFIX) &&
        symbols_to_keep.find(id) == symbols_to_keep.end())
      {
        i_it->turn_into_skip();
      }
    }
  }

  remove_skip(goto_functions);
}
