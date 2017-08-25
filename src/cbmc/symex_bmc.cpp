/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C

#include "symex_bmc.h"

#include <limits>

#include <util/source_location.h>
#include <util/simplify_expr.h>

symex_bmct::symex_bmct(
  const namespacet &_ns,
  symbol_tablet &_new_symbol_table,
  symex_targett &_target):
  goto_symext(_ns, _new_symbol_table, _target),
  record_coverage(false),
  max_unwind(0),
  max_unwind_is_set(false),
  symex_coverage(_ns)
{
}

/// show progress
void symex_bmct::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  const source_locationt &source_location=state.source.pc->source_location;

  if(!source_location.is_nil() && last_source_location!=source_location)
  {
    debug() << "BMC at file " << source_location.get_file()
            << " line " << source_location.get_line()
            << " function " << source_location.get_function()
            << eom;

    last_source_location=source_location;
  }

  const goto_programt::const_targett cur_pc=state.source.pc;
  const guardt cur_guard=state.guard;

  if(!state.guard.is_false() &&
     state.source.pc->is_assume() &&
     simplify_expr(state.source.pc->guard, ns).is_false())
  {
    statistics() << "aborting path on assume(false) at "
                 << state.source.pc->source_location
                 << " thread " << state.source.thread_nr;

    const irep_idt &c=state.source.pc->source_location.get_comment();
    if(!c.empty())
      statistics() << ": " << c;

    statistics() << eom;
  }

  goto_symext::symex_step(goto_functions, state);

  if(record_coverage &&
     // avoid an invalid iterator in state.source.pc
     (!cur_pc->is_end_function() ||
      cur_pc->function!=goto_functions.entry_point()))
  {
    // forward goto will effectively be covered via phi function,
    // which does not invoke symex_step; as symex_step is called
    // before merge_gotos, also state.guard will be false (we have
    // taken an impossible transition); thus we synthesize a
    // transition from the goto instruction to its target to make
    // sure the goto is considered covered
    if(cur_pc->is_goto() &&
       cur_pc->get_target()!=state.source.pc &&
       cur_pc->guard.is_true())
      symex_coverage.covered(cur_pc, cur_pc->get_target());
    else if(!state.guard.is_false())
      symex_coverage.covered(cur_pc, state.source.pc);
  }
}

void symex_bmct::merge_goto(
  const statet::goto_statet &goto_state,
  statet &state)
{
  const goto_programt::const_targett prev_pc=goto_state.source.pc;
  const guardt prev_guard=goto_state.guard;

  goto_symext::merge_goto(goto_state, state);

  assert(prev_pc->is_goto());
  if(record_coverage &&
     // could the branch possibly be taken?
     !prev_guard.is_false() &&
     !state.guard.is_false() &&
     // branches only, no single-successor goto
     !prev_pc->guard.is_true())
    symex_coverage.covered(prev_pc, state.source.pc);
}

bool symex_bmct::get_unwind(
  const symex_targett::sourcet &source,
  unsigned unwind)
{
  const irep_idt id=goto_programt::loop_id(source.pc);

  // We use the most specific limit we have,
  // and 'infinity' when we have none.

  unsigned this_loop_limit=std::numeric_limits<unsigned>::max();

  loop_limitst &this_thread_limits=
    thread_loop_limits[source.thread_nr];

  loop_limitst::const_iterator l_it=this_thread_limits.find(id);
  if(l_it!=this_thread_limits.end())
    this_loop_limit=l_it->second;
  else
  {
    l_it=loop_limits.find(id);
    if(l_it!=loop_limits.end())
      this_loop_limit=l_it->second;
    else if(max_unwind_is_set)
      this_loop_limit=max_unwind;
  }

  bool abort=unwind>=this_loop_limit;

  statistics() << (abort?"Not unwinding":"Unwinding")
               << " loop " << id << " iteration "
               << unwind;

  if(this_loop_limit!=std::numeric_limits<unsigned>::max())
    statistics() << " (" << this_loop_limit << " max)";

  statistics() << " " << source.pc->source_location
               << " thread " << source.thread_nr << eom;

  return abort;
}

bool symex_bmct::get_unwind_recursion(
  const irep_idt &id,
  const unsigned thread_nr,
  unsigned unwind)
{
  // We use the most specific limit we have,
  // and 'infinity' when we have none.

  unsigned this_loop_limit=std::numeric_limits<unsigned>::max();

  loop_limitst &this_thread_limits=
    thread_loop_limits[thread_nr];

  loop_limitst::const_iterator l_it=this_thread_limits.find(id);
  if(l_it!=this_thread_limits.end())
    this_loop_limit=l_it->second;
  else
  {
    l_it=loop_limits.find(id);
    if(l_it!=loop_limits.end())
      this_loop_limit=l_it->second;
    else if(max_unwind_is_set)
      this_loop_limit=max_unwind;
  }

  bool abort=unwind>this_loop_limit;

  if(unwind>0 || abort)
  {
    const symbolt &symbol=ns.lookup(id);

    statistics() << (abort?"Not unwinding":"Unwinding")
                 << " recursion "
                 << symbol.display_name()
                 << " iteration " << unwind;

    if(this_loop_limit!=std::numeric_limits<unsigned>::max())
      statistics() << " (" << this_loop_limit << " max)";

    statistics() << eom;
  }

  return abort;
}

void symex_bmct::no_body(const irep_idt &identifier)
{
  if(body_warnings.insert(identifier).second)
  {
    warning() <<
      "**** WARNING: no body for function " << identifier << eom;
  }
}
