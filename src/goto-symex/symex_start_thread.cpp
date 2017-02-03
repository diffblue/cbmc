/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <linking/zero_initializer.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_start_thread(statet &state)
{
  if(state.guard.is_false()) return;

  // we don't allow spawning threads out of atomic sections
  // this would require amendments to ordering constraints
  if(state.atomic_section_id!=0)
    throw "start_thread in atomic section detected";

  // record this
  target.spawn(state.guard.as_expr(), state.source);

  const goto_programt::instructiont &instruction=*state.source.pc;

  if(instruction.targets.size()!=1)
    throw "start_thread expects one target";

  goto_programt::const_targett thread_target=
    instruction.targets.front();

  // put into thread vector
  std::size_t t=state.threads.size();
  state.threads.push_back(statet::threadt());
  //statet::threadt &cur_thread=state.threads[state.source.thread_nr];
  statet::threadt &new_thread=state.threads.back();
  new_thread.pc=thread_target;
  new_thread.guard=state.guard;
  new_thread.priority=state.source.priority+1;
  new_thread.call_stack.push_back(state.top());
  new_thread.call_stack.back().local_objects.clear();
  new_thread.call_stack.back().goto_state_map.clear();
  #if 0
  new_thread.abstract_events=&(target.new_thread(cur_thread.abstract_events));
  #endif

  // create a copy of the local variables for the new thread
  statet::framet &frame=state.top();

  for(goto_symex_statet::renaming_levelt::current_namest::const_iterator
      c_it=state.level2.current_names.begin();
      c_it!=state.level2.current_names.end();
      ++c_it)
  {
    const irep_idt l1_o_id=c_it->second.first.get_l1_object_identifier();
    // could use iteration over local_objects as l1_o_id is prefix
    if(frame.local_objects.find(l1_o_id)==frame.local_objects.end())
      continue;

    // get original name
    ssa_exprt lhs(c_it->second.first.get_original_expr());

    // get L0 name for current thread
    lhs.set_level_0(t);

    // setup L1 name
    if(!state.level1.current_names.insert(
        std::make_pair(lhs.get_l1_object_identifier(),
                       std::make_pair(lhs, 0))).second)
      assert(false);
    state.rename(lhs, ns, goto_symex_statet::L1);
    const irep_idt l1_name=lhs.get_l1_object_identifier();
    // store it
    state.l1_history.insert(l1_name);
    new_thread.call_stack.back().local_objects.insert(l1_name);

    // make copy
    ssa_exprt rhs=c_it->second.first;
    state.rename(rhs, ns);

    guardt guard;
    symex_assign_symbol(state, lhs, nil_exprt(), rhs, guard, symex_targett::HIDDEN);
  }

  // initialize all variables marked thread-local
  const symbol_tablet &symbol_table=ns.get_symbol_table();

  forall_symbols(it, symbol_table.symbols)
  {
    const symbolt &symbol=it->second;

    if(!symbol.is_thread_local ||
       !symbol.is_static_lifetime ||
       (symbol.is_extern && symbol.value.is_nil()))
      continue;

    // get original name
    ssa_exprt lhs(symbol.symbol_expr());

    // get L0 name for current thread
    lhs.set_level_0(t);

    exprt rhs=symbol.value;
    if(rhs.is_nil())
      rhs=zero_initializer(symbol.type, symbol.location, ns);

    guardt guard;
    symex_assign_symbol(state, lhs, nil_exprt(), rhs, guard, symex_targett::HIDDEN);
  }
}
