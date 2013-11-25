/*******************************************************************\

Module: Branch Instrumentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include "function.h"
#include "branch.h"

/*******************************************************************\

Function: branch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void branch(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &id)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    // don't instrument our internal functions
    if(has_prefix(id2string(f_it->first), CPROVER_PREFIX))
      continue;
    
    // don't instrument the function to be called,
    // or otherwise this will be recursive
    if(f_it->first=="c::"+id2string(id))
      continue;
    
    // patch in a call to `id' at the branch points
    goto_programt &body=f_it->second.body;
    
    Forall_goto_program_instructions(i_it, body)
    {
      // if C goto T is transformed into:
      //
      // if !C goto T'          i_it
      // id("taken");           t1
      // goto T                 t2
      // T': id("not-taken");   t3
      // ...
    
      if(i_it->is_goto() &&
         !i_it->guard.is_constant())
      {
        // negate condition
        i_it->guard.make_not();
        
        goto_programt::targett t1=body.insert_after(i_it);
        t1->make_function_call(
          function_to_call(symbol_table, id, "taken"));
        t1->function=f_it->first;
        
        goto_programt::targett t2=body.insert_after(t1);
        t2->make_goto();
        t2->targets=i_it->targets;
        
        goto_programt::targett t3=body.insert_after(t2);
        t3->make_function_call(
          function_to_call(symbol_table, id, "not-taken"));
        t3->function=f_it->first;
        i_it->targets.clear();
        i_it->targets.push_back(t3);
      }    
    }
  }
}
