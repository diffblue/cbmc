/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "thread_instrumentation.h"

#include <util/c_types.h>
#include <util/string_constant.h>

#include <goto-programs/goto_model.h>

static bool has_start_thread(const goto_programt &goto_program)
{
  for(const auto &instruction : goto_program.instructions)
    if(instruction.is_start_thread())
      return true;

  return false;
}

void thread_exit_instrumentation(goto_programt &goto_program)
{
  if(goto_program.instructions.empty())
    return;

  // add assertion that all may flags for mutex-locked are gone
  // at the end
  goto_programt::targett end=goto_program.instructions.end();
  end--;

  assert(end->is_end_function());

  source_locationt source_location=end->source_location;
  irep_idt function=end->function;

  goto_program.insert_before_swap(end);

  const string_constantt mutex_locked_string("mutex-locked");

  binary_exprt get_may("get_may");

  // NULL is any
  get_may.op0()=null_pointer_exprt(pointer_type(empty_typet()));
  get_may.op1()=address_of_exprt(mutex_locked_string);

  end->make_assertion(not_exprt(get_may));

  end->source_location=source_location;
  end->source_location.set_comment("mutexes must not be locked on thread exit");
  end->function=function;
}

void thread_exit_instrumentation(goto_modelt &goto_model)
{
  // we'll look for START THREAD
  std::set<irep_idt> thread_fkts;

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(has_start_thread(f_it->second.body))
    {
      // now look for functions called

      for(const auto &instruction : f_it->second.body.instructions)
        if(instruction.is_function_call())
        {
          const exprt &function=
            to_code_function_call(instruction.code).function();
          if(function.id()==ID_symbol)
            thread_fkts.insert(to_symbol_expr(function).get_identifier());
        }
    }
  }

  // now instrument
  for(const auto &fkt : thread_fkts)
    thread_exit_instrumentation(
      goto_model.goto_functions.function_map[fkt].body);
}

void mutex_init_instrumentation(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  typet lock_type)
{
  symbol_tablet::symbolst::const_iterator f_it=
    symbol_table.symbols.find("__CPROVER_set_must");

  if(f_it==symbol_table.symbols.end())
    return;

  Forall_goto_program_instructions(it, goto_program)
  {
    if(it->is_assign())
    {
      const code_assignt &code_assign=
       to_code_assign(it->code);

      if(code_assign.lhs().type()==lock_type)
      {
        goto_programt::targett t=goto_program.insert_after(it);

        const code_function_callt call(
          f_it->second.symbol_expr(),
          {address_of_exprt(code_assign.lhs()),
           address_of_exprt(string_constantt("mutex-init"))});

        t->make_function_call(call);
        t->source_location=it->source_location;
      }
    }
  }
}

void mutex_init_instrumentation(goto_modelt &goto_model)
{
  // get pthread_mutex_lock

  symbol_tablet::symbolst::const_iterator f_it=
    goto_model.symbol_table.symbols.find("pthread_mutex_lock");

  if(f_it==goto_model.symbol_table.symbols.end())
    return;

  // get type of lock argument
  code_typet code_type=to_code_type(to_code_type(f_it->second.type));
  if(code_type.parameters().size()!=1)
    return;

  typet lock_type=code_type.parameters()[0].type();

  if(lock_type.id()!=ID_pointer)
    return;

  Forall_goto_functions(f_it, goto_model.goto_functions)
    mutex_init_instrumentation(
      goto_model.symbol_table,
      f_it->second.body,
      to_pointer_type(lock_type).subtype());
}
