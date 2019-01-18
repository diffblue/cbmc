/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#include "mmio.h"

#include <linking/static_lifetime_init.h>

#include "rw_set.h"

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#endif

static void mmio(
  value_setst &value_sets,
  const symbol_tablet &symbol_table,
  const irep_idt &function_id,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);

#ifdef LOCAL_MAY
  local_may_aliast local_may(goto_function);
#endif

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    if(instruction.is_assign())
    {
      rw_set_loct rw_set(
        ns,
        value_sets,
        function_id,
        i_it
#ifdef LOCAL_MAY
        ,
        local_may
#endif
      ); // NOLINT(whitespace/parens)

      if(rw_set.empty())
        continue;

      #if 0
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      const locationt &location=original_instruction.location;

      instruction.make_atomic_begin();
      instruction.location=location;
      i_it++;

      // we first perform (non-deterministically) up to 2 writes for
      // stuff that is potentially read
      forall_rw_set_entries(e_it, rw_set)
        if(e_it->second.r)
        {
          const shared_bufferst::varst &vars=
            shared_buffers(e_it->second.object);
          irep_idt choice0=shared_buffers.choice("0");
          irep_idt choice1=shared_buffers.choice("1");

          symbol_exprt choice0_expr=symbol_exprt(choice0, bool_typet());
          symbol_exprt choice1_expr=symbol_exprt(choice1, bool_typet());

          symbol_exprt w_buff0_expr=symbol_exprt(vars.w_buff0, vars.type);
          symbol_exprt w_buff1_expr=symbol_exprt(vars.w_buff1, vars.type);

          symbol_exprt w_used0_expr=symbol_exprt(vars.w_used0, bool_typet());
          symbol_exprt w_used1_expr=symbol_exprt(vars.w_used1, bool_typet());

          const side_effect_nondet_exprt nondet_bool_expr(bool_typet());

          const and_exprt choice0_rhs(nondet_bool_expr, w_used0_expr);
          const and_exprt choice1_rhs(nondet_bool_expr, w_used1_expr);

          // throw 2 Boolean dice
          shared_buffers.assignment(
            goto_program, i_it, location, choice0, choice0_rhs);
          shared_buffers.assignment(
            goto_program, i_it, location, choice1, choice1_rhs);

          const symbol_exprt lhs(e_it->second.object, vars.type);

          const if_exprt value(
            choice0_expr,
            w_buff0_expr,
            if_exprt(choice1_expr, w_buff1_expr, lhs));

          // write one of the buffer entries
          shared_buffers.assignment(
            goto_program, i_it, location, e_it->second.object, value);

          // update 'used' flags
          const if_exprt w_used0_rhs(choice0_expr, false_exprt(), w_used0_expr);
          const and_exprt w_used1_rhs(
            if_exprt(
              choice1_expr,
              false_exprt(),
              w_used1_expr),
            w_used0_expr);

          shared_buffers.assignment(
            goto_program, i_it, location, vars.w_used0, w_used0_rhs);
          shared_buffers.assignment(
            goto_program, i_it, location, vars.w_used1, w_used1_rhs);
        }

      // now rotate the write buffers for anything that is written
      forall_rw_set_entries(e_it, rw_set)
        if(e_it->second.w)
        {
          const shared_bufferst::varst &vars=
            shared_buffers(e_it->second.object);

          // w_used1=w_used0; w_used0=true;
          shared_buffers.assignment(
            goto_program, i_it, location, vars.w_used1, vars.w_used0);
          shared_buffers.assignment(
            goto_program, i_it, location, vars.w_used0, true_exprt());

          // w_buff1=w_buff0; w_buff0=RHS;
          shared_buffers.assignment(
            goto_program, i_it, location, vars.w_buff1, vars.w_buff0);
          shared_buffers.assignment(
            goto_program,
            i_it, location,
            vars.w_buff0,
            original_instruction.code.op1());
        }

      // ATOMIC_END
      i_it=goto_program.insert_before(i_it);
      i_it->make_atomic_end();
      i_it->location=location;
      i_it++;

      i_it--; // the for loop already counts us up
      #endif
    }
  }
}

void mmio(
  value_setst &value_sets,
  goto_modelt &goto_model)
{
  // now instrument

  Forall_goto_functions(f_it, goto_model.goto_functions)
    if(f_it->first != INITIALIZE_FUNCTION &&
       f_it->first!=goto_functionst::entry_point())
      mmio(
        value_sets,
        goto_model.symbol_table,
        f_it->first,
#ifdef LOCAL_MAY
        f_it->second,
#endif
        f_it->second.body);

  goto_model.goto_functions.update();
}
