/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_is_fresh.h"

#include <util/pointer_expr.h>
#include <util/symbol.h>

#include "dfcc_library.h"

dfcc_is_fresht::dfcc_is_fresht(dfcc_libraryt &library, messaget &log)
  : library(library), log(log)
{
}

void dfcc_is_fresht::rewrite_calls(
  goto_programt &program,
  const exprt &write_set)
{
  rewrite_calls(
    program,
    program.instructions.begin(),
    program.instructions.end(),
    write_set);
}

void dfcc_is_fresht::rewrite_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction, // excluding the last
  const exprt &write_set)
{
  auto &target = first_instruction;
  while(target != last_instruction)
  {
    if(target->is_function_call())
    {
      const auto &function = target->call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &fun_name = to_symbol_expr(function).get_identifier();

        if(fun_name == (is_fresh_id))
        {
          // add address on first operand
          target->call_arguments()[0] =
            address_of_exprt(target->call_arguments()[0]);

          // fix the function name.
          to_symbol_expr(target->call_function())
            .set_identifier(id2string(
              library.dfcc_fun_symbol.find(dfcc_funt::IS_FRESHR)->second.name));

          // pass the write_set
          target->call_arguments().push_back(write_set);
        }
        if(fun_name == (is_freshr_id))
        {
          // fix the function name.
          to_symbol_expr(target->call_function())
            .set_identifier(id2string(
              library.dfcc_fun_symbol.find(dfcc_funt::IS_FRESHR)->second.name));

          // pass the write_set
          target->call_arguments().push_back(write_set);
        }
      }
    }
    target++;
  }
}
