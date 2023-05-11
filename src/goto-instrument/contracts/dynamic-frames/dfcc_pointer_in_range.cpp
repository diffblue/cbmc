/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_pointer_in_range.h"

#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/replace_expr.h>
#include <util/std_code.h>
#include <util/symbol.h>

#include "dfcc_cfg_info.h"
#include "dfcc_library.h"

dfcc_pointer_in_ranget::dfcc_pointer_in_ranget(
  dfcc_libraryt &library,
  message_handlert &message_handler)
  : library(library), message_handler(message_handler), log(message_handler)
{
}

void dfcc_pointer_in_ranget::rewrite_calls(
  goto_programt &program,
  dfcc_cfg_infot cfg_info)
{
  rewrite_calls(
    program,
    program.instructions.begin(),
    program.instructions.end(),
    cfg_info);
}

void dfcc_pointer_in_ranget::rewrite_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  dfcc_cfg_infot cfg_info)
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

        if(fun_name == CPROVER_PREFIX "pointer_in_range_dfcc")
        {
          // add address on second operand
          target->call_arguments()[1] =
            address_of_exprt(target->call_arguments()[1]);

          // fix the function name.
          to_symbol_expr(target->call_function())
            .set_identifier(
              library.dfcc_fun_symbol[dfcc_funt::POINTER_IN_RANGE_DFCC].name);

          // pass the write_set
          target->call_arguments().push_back(cfg_info.get_write_set(target));
        }
      }
    }
    target++;
  }
}
