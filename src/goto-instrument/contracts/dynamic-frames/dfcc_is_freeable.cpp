/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/
#include "dfcc_is_freeable.h"

#include <util/symbol.h>

#include "dfcc_library.h"

dfcc_is_freeablet::dfcc_is_freeablet(dfcc_libraryt &library, messaget &log)
  : library(library), log(log)
{
}

void dfcc_is_freeablet::rewrite_calls(
  goto_programt &program,
  const exprt &write_set)
{
  rewrite_calls(
    program,
    program.instructions.begin(),
    program.instructions.end(),
    write_set);
}

void dfcc_is_freeablet::rewrite_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  const exprt &write_set)
{
  auto target = first_instruction;
  while(target != last_instruction)
  {
    if(target->is_function_call())
    {
      const auto &function = target->call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &fun_name = to_symbol_expr(function).get_identifier();

        if(fun_name == CPROVER_PREFIX "is_freeable")
        {
          // redirect call to library implementation
          to_symbol_expr(target->call_function())
            .set_identifier(library.get_dfcc_fun_name(dfcc_funt::IS_FREEABLE));
          target->call_arguments().push_back(write_set);
        }

        if(fun_name == CPROVER_PREFIX "is_freed")
        {
          // insert call to precondition for vacuity checking
          auto inst = goto_programt::make_function_call(
            code_function_callt{
              library
                .dfcc_fun_symbol
                  [dfcc_funt::REPLACE_ENSURES_IS_FREED_PRECONDITIONS]
                .symbol_expr(),
              {target->call_arguments().at(0), write_set}},
            target->source_location());
          program.insert_before_swap(target, inst);
          target++;

          // redirect call to library implementation
          to_symbol_expr(target->call_function())
            .set_identifier(library.get_dfcc_fun_name(dfcc_funt::IS_FREED));
          target->call_arguments().push_back(write_set);
        }
      }
    }
    target++;
  }
}
