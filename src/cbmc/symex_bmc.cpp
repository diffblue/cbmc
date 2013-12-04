/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/location.h>
#include <util/i2string.h>

#include "symex_bmc.h"

/*******************************************************************\

Function: symex_bmct::symex_bmct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_bmct::symex_bmct(
  const namespacet &_ns,
  symbol_tablet &_new_symbol_table,
  symex_targett &_target):
  goto_symext(_ns, _new_symbol_table, _target)
{
}

/*******************************************************************\

Function: symex_bmct::symex_step

  Inputs:

 Outputs:

 Purpose: show progress

\*******************************************************************/

void symex_bmct::symex_step(
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

  goto_symext::symex_step(goto_functions, state);
}

/*******************************************************************\

Function: symex_bmct::get_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmct::get_unwind(
  const symex_targett::sourcet &source,
  unsigned unwind)
{
  const irep_idt id=goto_programt::loop_id(source.pc);
  const long this_loop_max_unwind=
    std::max(max_unwind,
             std::max(thread_loop_limits[(unsigned)-1][id],
                      thread_loop_limits[source.thread_nr][id]));

  #if 1
  statistics() << "Unwinding loop " << id << " iteration "
               << unwind << " " << source.pc->location
               << " thread " << source.thread_nr << eom;
  #endif

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
