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

void slice_global_inits(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  // gather all functions reachable from the entry point

  call_grapht call_graph(goto_functions);
  const call_grapht::grapht &graph=call_graph.graph;

  std::list<irep_idt> worklist;
  std::unordered_set<irep_idt, irep_id_hash> functions_reached;

  const irep_idt entry_point=goto_functionst::entry_point();

  goto_functionst::function_mapt::const_iterator e_it;
  e_it=goto_functions.function_map.find(entry_point);

  if(e_it==goto_functions.function_map.end())
    throw "entry point not found";

  worklist.push_back(entry_point);

  do
  {
    const irep_idt id=worklist.front();
    worklist.pop_front();

    functions_reached.insert(id);

    const auto &p=graph.equal_range(id);

    for(auto it=p.first; it!=p.second; it++)
    {
      const irep_idt callee=it->second;

      if(functions_reached.find(callee)==functions_reached.end())
        worklist.push_back(callee);
    }
  }
  while(!worklist.empty());

  const irep_idt initialize=CPROVER_PREFIX "initialize";
  functions_reached.erase(initialize);

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

  assert(!functions_reached.empty());

  for(const irep_idt &id : functions_reached)
  {
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
  f_it=goto_functions.function_map.find(initialize);
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
