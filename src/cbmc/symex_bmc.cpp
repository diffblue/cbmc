/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/location.h>
#include <util/i2string.h>
#include <goto-symex/goto_trace.h>
#include <goto-symex/build_goto_trace.h>
#include <solvers/sat/satcheck.h>
#include <solvers/sat/satcheck_minisat2.h>

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
  loop_last_SSA_step(_target.SSA_steps.end())
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

Function: symex_bmct::convert

  Inputs: -

 Outputs: -

 Purpose: continue converting SSA steps where the last conversion stopped

\*******************************************************************/

void symex_bmct::convert() {    
  symex_target_equationt& e_target = dynamic_cast<symex_target_equationt&>(target); 
  if(loop_last_SSA_step == e_target.SSA_steps.end()) //first call
    loop_last_SSA_step = e_target.SSA_steps.begin();
  else {
    loop_last_SSA_step++;
  }
  loop_last_SSA_step = e_target.convert(prop_conv,loop_last_SSA_step);
}

/*******************************************************************\

Function: symex_bmct::current_activation_literal

  Inputs: -

 Outputs: current activation literal

 Purpose: get activation literal used for the assertions having been 
          translated in the most recent call to convert()

\*******************************************************************/

literalt symex_bmct::current_activation_literal() {
  symex_target_equationt& e_target = dynamic_cast<symex_target_equationt&>(target); 
  return prop_conv.prop.lnot(e_target.activate_assertions.back());
}

/*******************************************************************\

Function: symex_bmct::check_break

 Inputs: source of the current symbolic execution state

 Outputs: true if the back edge encountered during symbolic execution 
            corresponds to the given loop (incr_loop_id)

 Purpose: defines condition for interrupting symbolic execution 
            for incremental BMC

\*******************************************************************/

bool symex_bmct::check_break(const symex_targett::sourcet &source) {
  irep_idt id=(source.thread_nr!=0?(i2string(source.thread_nr)+":"):"")+
              id2string(source.pc->function)+"."+
              i2string(source.pc->loop_number);

  return (id==incr_loop_id);
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
  irep_idt id=(source.thread_nr!=0?(i2string(source.thread_nr)+":"):"")+
              id2string(source.pc->function)+"."+
              i2string(source.pc->loop_number);
  unsigned long this_loop_max_unwind=max_unwind;

  if(unwind_set.count(id)!=0)
    this_loop_max_unwind=unwind_set[id];

  if(this_loop_max_unwind==(unsigned long)-1) { //TODO just for test
    this_loop_max_unwind=max_unwind;
  }

  #if 1
  statistics() << "Unwinding loop " << id << " iteration "
               << unwind << " " << source.pc->location
               << " thread " << source.thread_nr << eom;
  #endif

  statistics() << "Unwind bound = " << this_loop_max_unwind << eom;


  return this_loop_max_unwind!=0 &&
         unwind>=this_loop_max_unwind;
}

/*******************************************************************\

Function: symex_bmct::get_unwind_recursion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmct::get_unwind_recursion(
  const irep_idt &identifier,
  unsigned unwind)
{
  unsigned long this_loop_max_unwind=max_unwind;

  #if 1
  if(unwind!=0)
  {
    const symbolt &symbol=ns.lookup(identifier);

    statistics() << "Unwinding recursion "
                 << symbol.display_name()
                 << " iteration " << unwind;
      
    if(this_loop_max_unwind!=0)
      statistics() << " (" << this_loop_max_unwind << " max)";

    statistics() << eom;
  }
  #endif

  return this_loop_max_unwind!=0 &&
         unwind>=this_loop_max_unwind;
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
