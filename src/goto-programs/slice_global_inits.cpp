/*******************************************************************\

Module: Remove initializations of unused global variables

Author: Daniel Poetzl

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove initializations of unused global variables

#include "slice_global_inits.h"

#include <unordered_set>

#include <analyses/call_graph.h>

#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_skip.h>

#include <linking/static_lifetime_init.h>

void slice_global_inits(goto_modelt &goto_model)
{
  // gather all functions reachable from the entry point
  const irep_idt entry_point=goto_functionst::entry_point();
  goto_functionst &goto_functions=goto_model.goto_functions;

  if(!goto_functions.function_map.count(entry_point))
    throw "entry point not found";

  // Get the call graph restricted to functions reachable from
  // the entry point:
  call_grapht call_graph =
    call_grapht::create_from_root_function(goto_model, entry_point, false);
  const auto directed_graph = call_graph.get_directed_graph();
  INVARIANT(
    !directed_graph.empty(), "At least __CPROVER_start should be reachable");

  // gather all symbols used by reachable functions

  class symbol_collectort:public const_expr_visitort
  {
  public:
    virtual void operator()(const exprt &expr)
    {
      if(expr.id()==ID_symbol)
      {
        const symbol_exprt &symbol_expr=to_symbol_expr(expr);
        const irep_idt id=symbol_expr.get_identifier();
        symbols.insert(id);
      }
    }

    std::unordered_set<irep_idt, irep_id_hash> symbols;
  };

  symbol_collectort visitor;

  for(std::size_t node_idx = 0; node_idx < directed_graph.size(); ++node_idx)
  {
    const irep_idt &id = directed_graph[node_idx].function;
    if(id == INITIALIZE_FUNCTION)
      continue;
    const goto_functionst::goto_functiont &goto_function
      =goto_functions.function_map.at(id);
    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      const codet &code=i_it->code;
      code.visit(visitor);
    }
  }

  const std::unordered_set<irep_idt, irep_id_hash> &symbols=visitor.symbols;

  // now remove unnecessary initializations

  goto_functionst::function_mapt::iterator f_it;
  f_it=goto_functions.function_map.find(INITIALIZE_FUNCTION);
  assert(f_it!=goto_functions.function_map.end());

  goto_programt &goto_program=f_it->second.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_assign())
    {
      const code_assignt &code_assign=to_code_assign(i_it->code);
      const symbol_exprt &symbol_expr=to_symbol_expr(code_assign.lhs());
      const irep_idt id=symbol_expr.get_identifier();

      if(!has_prefix(id2string(id), CPROVER_PREFIX) &&
         symbols.find(id)==symbols.end())
        i_it->make_skip();
    }
  }

  remove_skip(goto_functions);
  goto_functions.update();
}
