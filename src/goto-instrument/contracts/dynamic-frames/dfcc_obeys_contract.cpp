/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_obeys_contract.h"

#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/symbol.h>

#include <langapi/language_util.h>

#include "dfcc_cfg_info.h"
#include "dfcc_library.h"

dfcc_obeys_contractt::dfcc_obeys_contractt(
  dfcc_libraryt &library,
  message_handlert &message_handler)
  : library(library), message_handler(message_handler), log(message_handler)
{
}

void dfcc_obeys_contractt::rewrite_calls(
  goto_programt &program,
  dfcc_cfg_infot &cfg_info,
  std::set<irep_idt> &function_pointer_contracts)
{
  rewrite_calls(
    program,
    program.instructions.begin(),
    program.instructions.end(),
    cfg_info,
    function_pointer_contracts);
}

void dfcc_obeys_contractt::get_contract_name(
  const exprt &expr,
  std::set<irep_idt> &function_pointer_contracts)
{
  PRECONDITION(expr.id() == ID_typecast || expr.id() == ID_address_of);

  if(expr.id() == ID_typecast)
  {
    get_contract_name(to_typecast_expr(expr).op(), function_pointer_contracts);
  }
  else
  {
    PRECONDITION_WITH_DIAGNOSTICS(
      to_address_of_expr(expr).object().id() == ID_symbol,
      "symbol expression expected");
    function_pointer_contracts.insert(
      to_symbol_expr(to_address_of_expr(expr).object()).get_identifier());
  }
}

void dfcc_obeys_contractt::rewrite_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  dfcc_cfg_infot &cfg_info,
  std::set<irep_idt> &function_pointer_contracts)
{
  for(auto &target = first_instruction; target != last_instruction; target++)
  {
    if(target->is_function_call())
    {
      const auto &function = target->call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &fun_name = to_symbol_expr(function).get_identifier();

        if(has_prefix(id2string(fun_name), CPROVER_PREFIX "obeys_contract"))
        {
          // add address_of on first operand
          target->call_arguments()[0] =
            address_of_exprt(target->call_arguments()[0]);

          // fix the function name.
          to_symbol_expr(target->call_function())
            .set_identifier(
              library.dfcc_fun_symbol[dfcc_funt::OBEYS_CONTRACT].name);

          // pass the write_set
          target->call_arguments().push_back(cfg_info.get_write_set(target));

          // record discovered function contract
          get_contract_name(
            target->call_arguments()[1], function_pointer_contracts);
        }
      }
    }
  }
}
