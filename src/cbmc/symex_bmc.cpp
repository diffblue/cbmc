/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <location.h>
#include <i2string.h>

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
    print(9, "File "+location.get_string("file")+
             " line "+location.get_string("line")+
             " function "+location.get_string("function"));

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
  irep_idt id=(source.thread_nr!=0?(i2string(source.thread_nr)+":"):"")+
              id2string(source.pc->function)+"."+
              i2string(source.pc->loop_number);
  unsigned long this_loop_max_unwind=max_unwind;

  if(unwind_set.count(id)!=0)
    this_loop_max_unwind=unwind_set[id];

  #if 1
  {
    std::string msg=
      "Unwinding loop "+id2string(id)+" iteration "+i2string(unwind)+
      " "+source.pc->location.as_string()+
      " thread "+i2string(source.thread_nr);      
    print(8, msg);
  }
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
  const irep_idt &identifier,
  unsigned unwind)
{
  unsigned long this_loop_max_unwind=max_unwind;

  #if 1
  if(unwind!=0)
  {
    const symbolt &symbol=ns.lookup(identifier);
  
    std::string msg=
      "Unwinding recursion "+
      id2string(symbol.display_name())+
      " iteration "+i2string(unwind);
      
    if(this_loop_max_unwind!=0)
      msg+=" ("+i2string(this_loop_max_unwind)+" max)";

    print(8, msg);
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
    std::string msg=
      "**** WARNING: no body for function "+id2string(identifier);

    print(2, msg);
  }
}
