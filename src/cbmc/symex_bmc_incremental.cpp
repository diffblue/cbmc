/*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <limits>

#include <util/source_location.h>
#include <util/i2string.h>

#include "symex_bmc_incremental.h"

/*******************************************************************\

Function: symex_bmc_incrementalt::symex_bmct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_bmc_incrementalt::symex_bmc_incrementalt(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target)
  :
    symex_bmct(_ns, _new_symbol_table, _target)
{
#if 1
  magic_numbers.insert(0);
  magic_numbers.insert(1);
  magic_numbers.insert(2);
  magic_numbers.insert(6);
  magic_numbers.insert(12);
  magic_numbers.insert(17);
  magic_numbers.insert(21);
  magic_numbers.insert(40);
  magic_numbers.insert(60);
  magic_numbers.insert(80);
  magic_numbers.insert(100);
  magic_numbers.insert(200);
  magic_numbers.insert(1025);
#endif
}

/*******************************************************************\

Function: symex_bmc_incrementalt::get_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmc_incrementalt::get_unwind(
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

  // use the incremental limits if 
  // it is the specified incremental loop or
  // there was no non-incremental limit
  if(this_loop_limit==std::numeric_limits<unsigned>::max())
  {
    this_loop_limit = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
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

/*******************************************************************\

Function: symex_bmc_incrementalt::get_unwind_recursion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmc_incrementalt::get_unwind_recursion(
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

  // use the incremental limits if 
  // it is the specified incremental loop or
  // there was no non-incremental limit
  if(this_loop_limit==std::numeric_limits<unsigned>::max())
  {
    this_loop_limit = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
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

/*******************************************************************\

Function: symex_bmc_incrementalt::check_break

 Inputs: source of the current symbolic execution state

 Outputs: true if the back edge encountered during symbolic execution 
            corresponds to the a loop that is handled incrementally

 Purpose: defines condition for interrupting symbolic execution 
            for incremental BMC

\*******************************************************************/

bool symex_bmc_incrementalt::check_break(const irep_idt &id,
                             bool is_function, 
                             statet& state, 
                             const exprt &cond, 
                             unsigned unwind) 
{
  if(unwind < incr_min_unwind) return false;

#if 0
  std::cout << "loop limit for " << id 
            << (loop_limits.find(id)!=loop_limits.end() ? 
               " exists" : " does not exist") << std::endl;
#endif

  loop_limitst &this_thread_limits=
    thread_loop_limits[state.source.thread_nr];
  if(this_thread_limits.find(id)==this_thread_limits.end() &&
     loop_limits.find(id)==loop_limits.end()) 
  {
#if 0
    std::cout << "not statically unwound" << std::endl;
    //not a statically unwound loop when --incremental
#endif

    if(loop_cond.checked_function) 
    {
      loop_cond.checked_function = false;
      return false;
    }

#if 1
    if(options.get_bool_option("magic-numbers") &&
         magic_numbers.find(unwind)==magic_numbers.end())
    { 
      return false;
    }
#endif

    //memorise unwinding assertion for loop check
    exprt simplified_cond=not_exprt(cond);
    state.rename(simplified_cond, ns);
    do_simplify(simplified_cond);
    state.guard.guard_expr(simplified_cond);

    loop_cond.id = id;
    loop_cond.cond = simplified_cond;
    loop_cond.guard = state.guard.as_expr();
    loop_cond.loop_info = &(state.top().loop_iterations[id]);
    loop_cond.source = state.source;
    if(is_function) loop_cond.checked_function = true;

    return true;
  }

  return false;
}

/*******************************************************************\

Function: symex_bmc_incrementalt::add_loop_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmc_incrementalt::add_loop_check()
{
  status() << "Checking loop/recursive call " << loop_cond.id << eom;

#if 0
  debug() << "Loop/recursive call condition: " << from_expr(ns,"",loop_cond.cond) << eom;
#endif

  if(loop_cond.cond.is_false()) 
  {
    debug() << "Loop/recursive call " << loop_cond.id 
            << " not fully unwound" << eom;
    return false;
  }

  if(options.get_bool_option("earliest-loop-exit"))
    target.assertion(loop_cond.guard, not_exprt(loop_cond.cond), 
      "loop_condition_check", loop_cond.source);
  else 
    target.assertion(loop_cond.guard, loop_cond.cond, 
      "loop_condition_check", loop_cond.source);

  return true;
}

/*******************************************************************\

Function: symex_bmc_incrementalt::update_loop_info

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_bmc_incrementalt::update_loop_info(bool fully_unwound)
{
  status() << "Loop/recursive call " << loop_cond.id 
	  << (fully_unwound ? " fully unwound" : 
	      " not fully unwound") << eom;

  loop_cond.loop_info->fully_unwound = fully_unwound;
  loop_cond.id = "";
}
