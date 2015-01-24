/*******************************************************************\

Module: Nondeterministic initialization of certain global scope
        variables

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

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

      // is it a __CPROVER_* variable?
      if(has_prefix(id2string(sym.get_identifier()), CPROVER_PREFIX))
        continue;
        
      // static lifetime?
      if(!ns.lookup(sym.get_identifier()).is_static_lifetime)
        continue;

      // constant?
      if(sym.type().get_bool(ID_C_constant))
        continue;

      i_it=init.insert_before(++i_it);
      i_it->make_assignment();
      i_it->code=code_assignt(sym, side_effect_expr_nondett(sym.type()));
      i_it->source_location=instruction.source_location;
      i_it->function=instruction.function;
    }
    else if(instruction.is_function_call())
    {
      const code_function_callt &fct=to_code_function_call(instruction.code);
      const symbol_exprt &fsym=to_symbol_expr(fct.function());

      if(has_prefix(id2string(fsym.get_identifier()), "#ini#"))
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

