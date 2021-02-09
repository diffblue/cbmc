/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/exception_utils.h>
#include <util/expr_initializer.h>

#include "expr_skeleton.h"
#include "path_storage.h"
#include "symex_assign.h"

void goto_symext::symex_start_thread(statet &state)
{
  if(!state.reachable)
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
  state.threads.push_back(statet::threadt(guard_manager));
  // statet::threadt &cur_thread=state.threads[state.source.thread_nr];
  statet::threadt &new_thread=state.threads.back();
  new_thread.pc=thread_target;
  new_thread.function_id = state.source.function_id;
  new_thread.guard=state.guard;
  new_thread.call_stack.push_back(state.call_stack().top());
  new_thread.call_stack.back().local_objects.clear();
  new_thread.call_stack.back().goto_state_map.clear();
  #if 0
  new_thread.abstract_events=&(target.new_thread(cur_thread.abstract_events));
  #endif

  // create a copy of the local variables for the new thread
  framet &frame = state.call_stack().top();

  symex_renaming_levelt::viewt view;
  state.get_level2().current_names.get_view(view);

  for(const auto &pair : view)
  {
    const irep_idt l1_o_id = pair.second.first.get_l1_object_identifier();

    // could use iteration over local_objects as l1_o_id is prefix
    if(frame.local_objects.find(l1_o_id)==frame.local_objects.end())
      continue;

    // get original name
    ssa_exprt lhs(pair.second.first.get_original_expr());

    // get L0 name for current thread
    const renamedt<ssa_exprt, L0> l0_lhs = symex_level0(std::move(lhs), ns, t);
    const irep_idt &l0_name = l0_lhs.get().get_identifier();
    std::size_t l1_index = path_storage.get_unique_l1_index(l0_name, 0);
    CHECK_RETURN(l1_index == 0);

    // set up L1 name
    state.level1.insert(l0_lhs, 0);

    const ssa_exprt lhs_l1 = state.rename_ssa<L1>(l0_lhs.get(), ns).get();
    const irep_idt l1_name = lhs_l1.get_l1_object_identifier();
    // store it
    new_thread.call_stack.back().local_objects.insert(l1_name);

    // make copy
    ssa_exprt rhs = pair.second.first;

    exprt::operandst lhs_conditions;
    state.record_events.push(false);
    symex_assignt{
      state, symex_targett::assignment_typet::HIDDEN, ns, symex_config, target}
      .assign_symbol(lhs_l1, expr_skeletont{}, rhs, lhs_conditions);
    state.record_events.pop();
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

    exprt::operandst lhs_conditions;
    symex_assignt{
      state, symex_targett::assignment_typet::HIDDEN, ns, symex_config, target}
      .assign_symbol(lhs, expr_skeletont{}, rhs, lhs_conditions);
  }
}
