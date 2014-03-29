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
  prop_conv(_prop_conv),
  ui(ui_message_handlert::PLAIN),
  max_unwind_is_set(false)
{
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

bool symex_bmct::check_break(const symex_targett::sourcet &source,
                             unsigned unwind) {
  const irep_idt id=goto_programt::loop_id(source.pc);
  return (unwind>=incr_min_unwind) && (id==incr_loop_id);
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

  if(id==incr_loop_id)
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
