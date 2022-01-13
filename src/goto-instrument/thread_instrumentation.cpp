/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "thread_instrumentation.h"

#include <util/c_types.h>
#include <util/pointer_expr.h>
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

  source_locationt source_location = end->source_location();

  goto_program.insert_before_swap(end);

  const string_constantt mutex_locked_string("mutex-locked");

  // NULL is any
  binary_predicate_exprt get_may{
    null_pointer_exprt(pointer_type(empty_typet())),
    ID_get_may,
    address_of_exprt(mutex_locked_string)};

  *end = goto_programt::make_assertion(not_exprt(get_may), source_location);

  end->source_location_nonconst().set_comment(
    "mutexes must not be locked on thread exit");
}

void thread_exit_instrumentation(goto_modelt &goto_model)
{
  // we'll look for START THREAD
  std::set<irep_idt> thread_fkts;

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(has_start_thread(gf_entry.second.body))
    {
      // now look for functions called

      for(const auto &instruction : gf_entry.second.body.instructions)
        if(instruction.is_function_call())
        {
          const exprt &function = instruction.call_function();
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
  symbol_tablet::symbolst::const_iterator f_it =
    symbol_table.symbols.find(CPROVER_PREFIX "set_must");

  if(f_it==symbol_table.symbols.end())
    return;

  Forall_goto_program_instructions(it, goto_program)
  {
    if(it->is_assign())
    {
      if(it->assign_lhs().type() == lock_type)
      {
        const code_function_callt call(
          f_it->second.symbol_expr(),
          {address_of_exprt(it->assign_lhs()),
           address_of_exprt(string_constantt("mutex-init"))});

        goto_program.insert_after(
          it, goto_programt::make_function_call(call, it->source_location()));
      }
    }
  }
}

void mutex_init_instrumentation(goto_modelt &goto_model)
{
  // get pthread_mutex_lock

  symbol_tablet::symbolst::const_iterator lock_entry =
    goto_model.symbol_table.symbols.find("pthread_mutex_lock");

  if(lock_entry == goto_model.symbol_table.symbols.end())
    return;

  // get type of lock argument
  code_typet code_type = to_code_type(to_code_type(lock_entry->second.type));
  if(code_type.parameters().size()!=1)
    return;

  typet lock_type=code_type.parameters()[0].type();

  if(lock_type.id()!=ID_pointer)
    return;

  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    mutex_init_instrumentation(
      goto_model.symbol_table,
      gf_entry.second.body,
      to_pointer_type(lock_type).base_type());
  }
}
