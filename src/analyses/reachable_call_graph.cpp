/*******************************************************************\

Module: Reachable Call Graphs

Author:

\*******************************************************************/

/// \file
/// Reachable Call Graph
/// Constructs a call graph only from the functions reachable from a given
/// entry point, or the goto_functions.entry_point if none is given.

#include "reachable_call_graph.h"
#include <util/message.h>


reachable_call_grapht::reachable_call_grapht
(const goto_modelt & _goto_model)
{
  build(_goto_model.goto_functions);
}

void reachable_call_grapht::build(const goto_functionst & goto_functions)
{
  irep_idt start_function_name = goto_functions.entry_point();
  build(goto_functions, start_function_name);
}


void reachable_call_grapht::build(
    const goto_functionst & goto_functions,
    irep_idt start_function_name)
{
  std::set<irep_idt> working_queue;
  std::set<irep_idt> done;

  // start from entry point
  working_queue.insert(start_function_name);

  while(!working_queue.empty())
  {
    irep_idt caller=*working_queue.begin();
    working_queue.erase(working_queue.begin());

    if(!done.insert(caller).second)
      continue;

    const goto_functionst::function_mapt::const_iterator f_it=
      goto_functions.function_map.find(caller);

    if(f_it==goto_functions.function_map.end())
      continue;

    const goto_programt &program=
      f_it->second.body;

    forall_goto_program_instructions(i_it, program)
    {
      if(i_it->is_function_call())
      {
        const exprt &function_expr=to_code_function_call(i_it->code).function();
        if(function_expr.id()==ID_symbol)
        {
          irep_idt callee = to_symbol_expr(function_expr).get_identifier();
          add(caller, callee);
          working_queue.insert(callee);
        }
      }
    }
  }
}


std::unordered_set<irep_idt, irep_id_hash>
reachable_call_grapht::backward_slice(irep_idt destination_function)
{
  std::unordered_set<irep_idt, irep_id_hash> result;
  std::list<node_indext> worklist;
  for(node_indext idx=0; idx<nodes.size(); idx++)
  {
    if(nodes[idx].function_name==destination_function)
    {
      worklist.push_back(idx);
      break;
    }
  }
  INVARIANT(!worklist.empty(), "destination function not found");

  while(!worklist.empty())
  {
    const node_indext id = worklist.front();
    worklist.pop_front();

    result.insert(nodes[id].function_name);
    for(const auto o : nodes[id].in)
    {
      if(result.find(nodes[o.first].function_name)==result.end())
          worklist.push_back(o.first);
    }
  }

return result;
}

