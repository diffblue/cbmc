/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ansi-c/string_constant.h>

#include "thread_exit_instrumentation.h"

/*******************************************************************\

Function: has_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_start_thread(const goto_programt &goto_program)
{
  for(const auto &instruction : goto_program.instructions)
    if(instruction.is_start_thread())
      return true;

  return false;
}

/*******************************************************************\

Function: thread_exit_instrumentation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void thread_exit_instrumentation(goto_programt &goto_program)
{
  if(goto_program.instructions.empty()) return;

  // add assertion that all may flags for mutex-locked are gone
  // at the end
  goto_programt::targett end=goto_program.instructions.end();
  end--;

  assert(end->is_end_function());
  
  source_locationt source_location=end->source_location;
  irep_idt function=end->function;

  goto_program.insert_before_swap(end);

  exprt mutex_locked_string=
    string_constantt("mutex-locked");
  
  binary_exprt get_may("get_may");
  
  // NULL is any
  get_may.op0()=constant_exprt(ID_NULL, pointer_typet(empty_typet()));
  get_may.op1()=address_of_exprt(mutex_locked_string);
  
  end->make_assertion(get_may);

  end->source_location=source_location;
  end->source_location.set_comment("mutexes must not be locked on thread exit");
  end->function=function;
}

/*******************************************************************\

Function: thread_exit_instrumentation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void thread_exit_instrumentation(goto_functionst &goto_functions)
{
  // we'll look for START THREAD
  std::set<irep_idt> thread_fkts;
  
  forall_goto_functions(f_it, goto_functions)
  {
    if(has_start_thread(f_it->second.body))
    {
      // now look for functions called

      for(const auto &instruction : f_it->second.body.instructions)
        if(instruction.is_function_call())
        {
          const exprt &function=to_code_function_call(instruction.code).function();
          if(function.id()==ID_symbol)
            thread_fkts.insert(to_symbol_expr(function).get_identifier());
        }
    }
  }

  // now instrument
  for(const auto &fkt : thread_fkts)
  {
    thread_exit_instrumentation(goto_functions.function_map[fkt].body);
  }
}
