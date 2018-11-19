/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/exception_utils.h>

void goto_symext::symex_atomic_begin(statet &state)
{
  if(state.guard.is_false())
    return;

  if(state.atomic_section_id != 0)
    throw incorrect_goto_program_exceptiont(
      "we don't support nesting of atomic sections",
      state.source.pc->source_location);

  state.atomic_section_id=++atomic_section_counter;
  state.read_in_atomic_section.clear();
  state.written_in_atomic_section.clear();

  target.atomic_begin(
      state.guard.as_expr(),
      atomic_section_counter,
      state.source);
}

void goto_symext::symex_atomic_end(statet &state)
{
  if(state.guard.is_false())
    return;

  if(state.atomic_section_id == 0)
    throw incorrect_goto_program_exceptiont(
      "ATOMIC_END unmatched", state.source.pc->source_location);

  const unsigned atomic_section_id=state.atomic_section_id;
  state.atomic_section_id=0;

  for(const auto &pair : state.read_in_atomic_section)
  {
    ssa_exprt r = pair.first;
    r.set_level_2(pair.second.first);

    // guard is the disjunction over reads
    PRECONDITION(!pair.second.second.empty());
    guardt read_guard(pair.second.second.front());
    for(std::list<guardt>::const_iterator it = ++(pair.second.second.begin());
        it != pair.second.second.end();
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

  for(const auto &pair : state.written_in_atomic_section)
  {
    ssa_exprt w = pair.first;
    w.set_level_2(state.level2.current_count(w.get_identifier()));

    // guard is the disjunction over writes
    PRECONDITION(!pair.second.empty());
    guardt write_guard(pair.second.front());
    for(std::list<guardt>::const_iterator it = ++(pair.second.begin());
        it != pair.second.end();
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
