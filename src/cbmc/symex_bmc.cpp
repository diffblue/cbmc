/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <limits>

#include <util/location.h>
#include <util/i2string.h>
#include <util/xml.h>
#include <goto-programs/goto_trace.h>
#include <goto-symex/build_goto_trace.h>
#include <solvers/sat/satcheck.h>
#include <solvers/sat/satcheck_minisat2.h>
#include <solvers/prop/literal.h>

#include "symex_bmc.h"
#include "bv_cbmc.h"
#include <iostream>

/*******************************************************************\

Function: symex_bmct::symex_bmct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_bmct::symex_bmct(
  const namespacet &_ns,
  symbol_tablet &_new_symbol_table,
  symex_targett &_target,
  prop_convt& _prop_conv):
  goto_symext(_ns, _new_symbol_table, _target),
  is_incremental(false),
  prop_conv(_prop_conv),
  ui(ui_message_handlert::PLAIN),
  max_unwind_is_set(false)
{
  loop_cond.checked_function = false;

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
  magic_numbers.insert(120);
  magic_numbers.insert(140);
  magic_numbers.insert(160);
  magic_numbers.insert(180);
  magic_numbers.insert(200);
#endif
}


/*******************************************************************\

Function: symex_bmct::symex_step

  Inputs: goto functions, current symbolic execution state

 Outputs: true if symbolic execution is to be interrupted to perform incremental checking

 Purpose: show progress

\*******************************************************************/

bool symex_bmct::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  const locationt &location=state.source.pc->location;

  if(!location.is_nil() && last_location!=location)
  {
    debug() << "BMC at file " << location.get_file()
            << " line " << location.get_line()
            << " function " << location.get_function()
            << eom;

    last_location=location;
  }

  return goto_symext::symex_step(goto_functions, state);
}

/*******************************************************************\

Function: symex_bmct::check_break

 Inputs: source of the current symbolic execution state

 Outputs: true if the back edge encountered during symbolic execution 
            corresponds to the given loop (incr_loop_id)

 Purpose: defines condition for interrupting symbolic execution 
            for incremental BMC

\*******************************************************************/

bool symex_bmct::check_break(const irep_idt &id,
                             bool is_function, 
                             statet& state, 
                             const exprt &cond, 
                             unsigned unwind) 
{
  if(!is_incremental) return false;
  if(unwind < incr_min_unwind) return false;

#if 0
  std::cout << "loop limit for " << id 
            << (loop_limits.find(id)!=loop_limits.end() ? 
               " exists" : " does not exist") << std::endl;
#endif

  loop_limitst &this_thread_limits=
    thread_loop_limits[state.source.thread_nr];
  if(incr_loop_id=="" && 
     this_thread_limits.find(id)==this_thread_limits.end() &&
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

  //loop specified by --incremental-check
  return (id == incr_loop_id);
}

bool symex_bmct::add_loop_check()
{
  if(loop_cond.id=="") return false;

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

void symex_bmct::update_loop_info(bool fully_unwound)
{
  if(loop_cond.id=="") return;

  status() << "Loop/recursive call " << loop_cond.id 
	  << (fully_unwound ? " fully unwound" : " not fully unwound") << eom;

  loop_cond.loop_info->fully_unwound = fully_unwound;
  loop_cond.id = "";
}


/*******************************************************************\

Function: symex_bmct::get_unwind

  Inputs: source of the current symbolic execution state, symex unwind counter

 Outputs: true if loop bound has been exceeded 

 Purpose: check whether loop bound for current loop has been reached

\*******************************************************************/

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

  // use the incremental limits if 
  // it is the specified incremental loop or
  // there was no non-incremental limit
  if(id==incr_loop_id || 
     (incr_loop_id=="" && is_incremental && 
      this_loop_limit==std::numeric_limits<unsigned>::max()))
  {
    this_loop_limit = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
  }

  bool abort=unwind>=this_loop_limit;

  // report where we are  
  if(ui==ui_message_handlert::XML_UI)
  {
    xmlt xml("current-unwinding");
    xml.data=i2string(unwind);
    std::cout << xml << "\n";
  }

  statistics() << (abort?"Not unwinding":"Unwinding")
               << " loop " << id << " iteration "
               << unwind;

  if(this_loop_limit!=std::numeric_limits<unsigned>::max())
    statistics() << " (" << this_loop_limit << " max)";

  statistics() << " " << source.pc->location
               << " thread " << source.thread_nr << eom;
  return abort;
}

/*******************************************************************\

Function: symex_bmct::get_unwind_recursion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

  if(id==incr_loop_id || 
     (incr_loop_id=="" && is_incremental && 
      this_loop_limit==std::numeric_limits<unsigned>::max()))
  {
    this_loop_limit = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
  }

  bool abort=unwind>=this_loop_limit;

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

Function: symex_bmct::no_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_bmct::no_body(const irep_idt &identifier)
{
  if(body_warnings.insert(identifier).second)
  {
    warning() <<
      "**** WARNING: no body for function " << identifier << eom;
  }
}
