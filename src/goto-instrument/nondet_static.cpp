/*******************************************************************\

Module: Nondeterministic initialization of certain global scope
        variables

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Nondeterministic initialization of certain global scope variables

#include "nondet_static.h"

#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

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

      // any other internal variable such as Java specific?
      if(
        ns.lookup(sym.get_identifier())
          .type.get_bool(ID_C_no_nondet_initialization))
      {
        continue;
      }

      // static lifetime?
      if(!ns.lookup(sym.get_identifier()).is_static_lifetime)
        continue;

      // constant?
      if(is_constant_or_has_constant_components(sym.type(), ns))
        continue;

      const goto_programt::instructiont original_instruction = instruction;
      i_it->make_assignment();
      i_it->code=code_assignt(sym, side_effect_expr_nondett(sym.type()));
      i_it->source_location = original_instruction.source_location;
      i_it->function = original_instruction.function;
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

void nondet_static(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  nondet_static(ns, goto_functions, INITIALIZE_FUNCTION);

  // update counters etc.
  goto_functions.update();
}

void nondet_static(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  nondet_static(ns, goto_model.goto_functions);
}
