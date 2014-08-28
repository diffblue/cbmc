/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <limits>

#include <util/source_location.h>
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
  goto_symext(_ns, _new_symbol_table, _target),
  max_unwind_is_set(false)
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
  const source_locationt &source_location=state.source.pc->source_location;

  if(!source_location.is_nil() && last_source_location!=source_location)
  {
    debug() << "BMC at file " << source_location.get_file()
            << " line " << source_location.get_line()
            << " function " << source_location.get_function()
            << eom;

    last_source_location=source_location;
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
