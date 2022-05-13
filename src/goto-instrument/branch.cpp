/*******************************************************************\

Module: Branch Instrumentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Branch Instrumentation

#include "branch.h"

#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/prefix.h>

#include <goto-programs/goto_model.h>

#include "function.h"

void branch(
  goto_modelt &goto_model,
  const irep_idt &id)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    // don't instrument our internal functions
    if(has_prefix(id2string(gf_entry.first), CPROVER_PREFIX))
      continue;

    // don't instrument the function to be called,
    // or otherwise this will be recursive
    if(gf_entry.first == id)
      continue;

    // patch in a call to `id' at the branch points
    goto_programt &body = gf_entry.second.body;

    Forall_goto_program_instructions(i_it, body)
    {
      // if C goto T is transformed into:
      //
      // if !C goto T'          i_it
      // id("taken");           t1
      // goto T                 t2
      // T': id("not-taken");   t3
      // ...

      if(i_it->is_goto() && !i_it->condition().is_constant())
      {
        // negate condition
        i_it->condition_nonconst() = boolean_negate(i_it->condition());

        goto_programt::targett t1 = body.insert_after(
          i_it,
          goto_programt::make_function_call(
            function_to_call(goto_model.symbol_table, id, "taken")));

        goto_programt::targett t2 = body.insert_after(
          t1, goto_programt::make_goto(i_it->get_target(), true_exprt()));

        goto_programt::targett t3 = body.insert_after(
          t2,
          goto_programt::make_function_call(
            function_to_call(goto_model.symbol_table, id, "not-taken")));
        i_it->targets.clear();
        i_it->targets.push_back(t3);
      }
    }
  }
}
