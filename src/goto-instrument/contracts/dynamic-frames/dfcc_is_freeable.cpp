/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/
#include "dfcc_is_freeable.h"

#include <util/cprover_prefix.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "dfcc_cfg_info.h"
#include "dfcc_library.h"

dfcc_is_freeablet::dfcc_is_freeablet(
  dfcc_libraryt &library,
  message_handlert &message_handler)
  : library(library), message_handler(message_handler)
{
}

void dfcc_is_freeablet::rewrite_calls(
  goto_programt &program,
  dfcc_cfg_infot &cfg_info)
{
  rewrite_calls(
    program,
    program.instructions.begin(),
    program.instructions.end(),
    cfg_info);
}

void dfcc_is_freeablet::rewrite_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  dfcc_cfg_infot &cfg_info)
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
          target->call_arguments().push_back(cfg_info.get_write_set(target));
        }
        else if(fun_name == CPROVER_PREFIX "was_freed")
        {
          // insert call to precondition for vacuity checking
          auto inst = goto_programt::make_function_call(
            library.check_replace_ensures_was_freed_preconditions_call(
              target->call_arguments().at(0),
              cfg_info.get_write_set(target),
              target->source_location()),
            target->source_location());
          program.insert_before_swap(target, inst);
          target++;

          // redirect call to library implementation
          to_symbol_expr(target->call_function())
            .set_identifier(library.get_dfcc_fun_name(dfcc_funt::WAS_FREED));
          target->call_arguments().push_back(cfg_info.get_write_set(target));
        }
      }
    }
    target++;
  }
}
