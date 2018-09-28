/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/exception_utils.h>
#include <util/expr_initializer.h>

void goto_symext::symex_start_thread(statet &state)
{
  if(state.guard.is_false())
    return;

  if(state.atomic_section_id != 0)
    throw incorrect_goto_program_exceptiont(
      "spawning threads out of atomic sections is not allowed; "
      "this would require amendments to ordering constraints",
      state.source.pc->source_location);

  // record this
  target.spawn(state.guard.as_expr(), state.source);

  const goto_programt::instructiont &instruction=*state.source.pc;

  INVARIANT(instruction.targets.size() == 1, "start_thread expects one target");

  goto_programt::const_targett thread_target=
    instruction.get_target();

  // put into thread vector
  std::size_t t=state.threads.size();
  state.threads.push_back(statet::threadt());
  // statet::threadt &cur_thread=state.threads[state.source.thread_nr];
  statet::threadt &new_thread=state.threads.back();
  new_thread.pc=thread_target;
  new_thread.guard=state.guard;
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

    // set up L1 name
    if(!state.level1.current_names.insert(
        std::make_pair(lhs.get_l1_object_identifier(),
                       std::make_pair(lhs, 0))).second)
      UNREACHABLE;
    state.rename(lhs, ns, goto_symex_statet::L1);
    const irep_idt l1_name=lhs.get_l1_object_identifier();
    // store it
    state.l1_history.insert(l1_name);
    new_thread.call_stack.back().local_objects.insert(l1_name);

    // make copy
    ssa_exprt rhs=c_it->second.first;

    guardt guard;
    const bool record_events=state.record_events;
    state.record_events=false;
    symex_assign_symbol(
      state,
      lhs,
      nil_exprt(),
      rhs,
      guard,
      symex_targett::assignment_typet::HIDDEN);
    state.record_events=record_events;
  }

  // initialize all variables marked thread-local
  const symbol_tablet &symbol_table=ns.get_symbol_table();

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    const symbolt &symbol = symbol_pair.second;

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
    {
      const auto zero = zero_initializer(symbol.type, symbol.location, ns);
      CHECK_RETURN(zero.has_value());
      rhs = *zero;
    }

    guardt guard;
    symex_assign_symbol(
      state,
      lhs,
      nil_exprt(),
      rhs,
      guard,
      symex_targett::assignment_typet::HIDDEN);
  }
}
