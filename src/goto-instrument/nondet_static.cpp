/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

#include <namespace.h>
#include <std_expr.h>
#include <cprover_prefix.h>
#include <prefix.h>

#include <goto-programs/goto_functions.h>

#include "nondet_static.h"

/*******************************************************************\

Function: nondet_static

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_static(
  const namespacet &ns,
  goto_functionst &goto_functions,
  const irep_idt &fct_name)
{
  goto_functionst::function_mapt::iterator
    i_it=goto_functions.function_map.find(fct_name);
  assert(i_it!=goto_functions.function_map.end());

  goto_programt &init=i_it->second.body;

  Forall_goto_program_instructions(i_it, init)
  {
    const goto_programt::instructiont &instruction=*i_it;

    if(instruction.is_assign())
    {
      const symbol_exprt &sym=to_symbol_expr(
          to_code_assign(instruction.code).lhs());
      if(has_prefix(sym.get_identifier().as_string(), CPROVER_PREFIX) ||
          !ns.lookup(sym.get_identifier()).is_static_lifetime)
        continue;

      i_it=init.insert_before(++i_it);
      i_it->make_assignment();
      i_it->code=code_assignt(sym, nondet_exprt(sym.type()));
      i_it->location=instruction.location;
      i_it->function=instruction.function;
    }
    else if(instruction.is_function_call())
    {
      const code_function_callt &fct=to_code_function_call(instruction.code);
      const symbol_exprt &fsym=to_symbol_expr(fct.function());

      if(has_prefix(fsym.get_identifier().as_string(), "c::#ini#"))
        nondet_static(ns, goto_functions, fsym.get_identifier());
    }
  }
}


/*******************************************************************\

Function: nondet_static

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_static(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  nondet_static(ns, goto_functions, CPROVER_PREFIX "initialize");

  // update counters etc.
  goto_functions.update();
}

