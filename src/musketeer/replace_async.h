/*******************************************************************\

Module:

Author: Vincent Nimal

Date: December 2013

\*******************************************************************/

#ifndef REPLACE_ASYNC_H
#define REPLACE_ASYNC_H

#include <goto-programs/goto_program.h>
#include <util/std_code.h>

class goto_functionst;
class namespacet;

void replace_async(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    goto_programt& program=f_it->second.body;

    Forall_goto_program_instructions(i_it, program)
    {
      const goto_programt::instructiont &instruction=*i_it;

      if(instruction.is_function_call())
      {
        const code_function_callt &fct=to_code_function_call(instruction.code);
        if(fct.function().id() == ID_symbol)
        {
          const symbol_exprt &fsym=to_symbol_expr(fct.function());
           
          if(ns.lookup(fsym.get_identifier()).base_name == "pthread_create")
          {
            assert(fct.arguments().size()>=4);
            code_function_callt new_call;
            /* takes the 3rd argument (pointer to the function to call) */
            const exprt& fct_name=fct.arguments()[2];

            if(fct_name.id()==ID_address_of) {
              /* pointer to function */
              new_call.function()=to_address_of_expr(fct.arguments()[2]).object();
            }
            else {
              /* other (e.g. local copy) */
              new_call.function()=fct_name;
            }

            new_call.arguments().resize(1);
            /* takes the 4th argument (argument of the function to call) */
            new_call.arguments()[0]=fct.arguments()[3];

            /* __CPROVER_ASYNC labels only evaluated at C parsing time; we 
               reproduce here the effects of the evaluation of this label */
            i_it->labels.push_front("__CPROVER_ASYNC_0");
            i_it->clear(START_THREAD);
            /* CP_AC_0: f(); -> CP_AC_0: start_th; goto 2; 1: f(); end_th; 2: ... */

            goto_programt::targett goto2=program.insert_after(i_it);
            goto_programt::targett call=program.insert_after(goto2);
            goto_programt::targett end=program.insert_after(call);
            goto_programt::targett skip=program.insert_after(end);

            goto2->make_goto(skip);
            call->make_function_call(new_call);
            end->clear(END_THREAD);
            skip->make_skip();
          }
        }
      }
    }
  }
}

#endif
