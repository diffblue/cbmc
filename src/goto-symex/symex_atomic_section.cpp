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
  if(state.guard.is_false())
    return;

  // we don't allow any nesting of atomic sections
  if(state.atomic_section_id!=0)
    throw "nested atomic section detected at "+
      state.source.pc->source_location.as_string();

  state.atomic_section_id=++atomic_section_counter;
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
  if(state.guard.is_false())
    return;

  if(state.atomic_section_id==0)
    throw "ATOMIC_END unmatched"; // NOLINT(readability/throw)

  const unsigned atomic_section_id=state.atomic_section_id;
  state.atomic_section_id=0;

  for(goto_symex_statet::read_in_atomic_sectiont::const_iterator
      r_it=state.read_in_atomic_section.begin();
      r_it!=state.read_in_atomic_section.end();
      ++r_it)
  {
    ssa_exprt r=r_it->first;
    r.set_level_2(r_it->second.first);

    // guard is the disjunction over reads
    assert(!r_it->second.second.empty());
    guardt read_guard(r_it->second.second.front());
    for(std::list<guardt>::const_iterator
        it=++(r_it->second.second.begin());
        it!=r_it->second.second.end();
        ++it)
      read_guard|=*it;
    exprt read_guard_expr=read_guard.as_expr();
    do_simplify(read_guard_expr);

    target.shared_read(
      read_guard_expr,
      r,
      atomic_section_id,
      state.source);
  }

  for(goto_symex_statet::written_in_atomic_sectiont::const_iterator
      w_it=state.written_in_atomic_section.begin();
      w_it!=state.written_in_atomic_section.end();
      ++w_it)
  {
    ssa_exprt w=w_it->first;
    w.set_level_2(state.level2.current_count(w.get_identifier()));

    // guard is the disjunction over writes
    assert(!w_it->second.empty());
    guardt write_guard(w_it->second.front());
    for(std::list<guardt>::const_iterator
        it=++(w_it->second.begin());
        it!=w_it->second.end();
        ++it)
      write_guard|=*it;
    exprt write_guard_expr=write_guard.as_expr();
    do_simplify(write_guard_expr);

    target.shared_write(
      write_guard_expr,
      w,
      atomic_section_id,
      state.source);
  }

  target.atomic_end(
    state.guard.as_expr(),
    atomic_section_id,
    state.source);
}
