/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_atomic_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_atomic_begin(statet &state)
{
  if(state.guard.is_false()) return;

  // we don't allow any nesting of atomic sections
  if(state.atomic_section_id!=0)
    throw "nested atomic section detected";
    
  state.atomic_section_id=++atomic_section_counter;
  atomic_section_entry_guard=state.guard;
  state.level2_at_atomic_section_entry=state.level2;
  state.read_in_atomic_section.clear();
  state.written_in_atomic_section.clear();
  target.atomic_begin(
      state.guard.as_expr(),
      atomic_section_counter,
      state.source);
}

/*******************************************************************\

Function: goto_symext::symex_atomic_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_atomic_end(statet &state)
{
  if(state.guard.is_false()) return;
  
  if(state.atomic_section_id==0)
    throw "ATOMIC_END unmatched";
  
  const unsigned atomic_section_id=state.atomic_section_id;
  state.atomic_section_id=0;

  state.guard.swap(atomic_section_entry_guard);
  for(hash_map_cont<irep_idt, irep_idt, irep_id_hash>::const_iterator
      r_it=state.read_in_atomic_section.begin();
      r_it!=state.read_in_atomic_section.end();
      ++r_it)
  {
    const irep_idt &orig_identifier=r_it->first;

    const typet &type=ns.lookup(orig_identifier).type;
    symbol_exprt r(r_it->second, type);

    // properly rename type, if necessary
    const bool record_events=state.record_events;
    state.record_events=false;
    state.rename(r, ns, goto_symex_statet::L2);
    state.record_events=record_events;

    symbol_exprt original_symbol(orig_identifier, r.type());
    target.shared_read(
      state.guard.as_expr(),
      r,
      original_symbol,
      atomic_section_id,
      state.source);
  }
  state.guard.swap(atomic_section_entry_guard);

  for(hash_set_cont<irep_idt, irep_id_hash>::const_iterator
      w_it=state.written_in_atomic_section.begin();
      w_it!=state.written_in_atomic_section.end();
      ++w_it)
  {
    const irep_idt &orig_identifier=*w_it;

    const typet &type=ns.lookup(orig_identifier).type;
    symbol_exprt w(orig_identifier, type);

    const bool record_events=state.record_events;
    state.record_events=false;
    state.rename(w, ns, goto_symex_statet::L1);
    state.rename(w.type(), ns, goto_symex_statet::L2);
    const irep_idt new_name=state.level2(w.get_identifier());
    w.set_identifier(new_name);
    state.record_events=record_events;

    symbol_exprt original_symbol(orig_identifier, w.type());
    target.shared_write(
      state.guard.as_expr(),
      w,
      original_symbol,
      atomic_section_id,
      state.source);
  }

  target.atomic_end(
    state.guard.as_expr(),
    atomic_section_id,
    state.source);
}
