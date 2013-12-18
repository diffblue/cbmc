/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/location.h>
#include <util/i2string.h>
#include <util/xml.h>
#include <goto-symex/goto_trace.h>
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
  symex_target_equationt &_target,
  prop_convt& _prop_conv):
  goto_symext(_ns, _new_symbol_table, _target),
  prop_conv(_prop_conv),
  ui(ui_message_handlert::PLAIN)
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
  long this_loop_max_unwind=
    std::max(max_unwind,
             std::max(thread_loop_limits[(unsigned)-1][id],
                      thread_loop_limits[source.thread_nr][id]));

  if(id==incr_loop_id) {
    this_loop_max_unwind = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
  }

  #if 1
  statistics() << "Unwinding loop " << id << " iteration "
               << unwind << " " << source.pc->location
               << " thread " << source.thread_nr << eom;

  if(ui==ui_message_handlert::XML_UI) {
      xmlt xml("current-unwinding");
      xml.data=i2string(unwind);
      std::cout << xml;
      std::cout << "\n";
  }
  #endif

  #if 0
    statistics() << "Unwind bound = " << this_loop_max_unwind << eom;
  #endif

  return unwind>=this_loop_max_unwind;
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
  const long this_loop_max_unwind=
    std::max(max_unwind,
             std::max(thread_loop_limits[(unsigned)-1][id],
                      thread_loop_limits[thread_nr][id]));

  #if 1
  if(unwind!=0)
  {
    const symbolt &symbol=ns.lookup(id);

    statistics() << "Unwinding recursion "
                 << symbol.display_name()
                 << " iteration " << unwind;
      
    if(this_loop_max_unwind!=0)
      statistics() << " (" << this_loop_max_unwind << " max)";

    statistics() << eom;
  }
  #endif

  return unwind>=this_loop_max_unwind;
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
