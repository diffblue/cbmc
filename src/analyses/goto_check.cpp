/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// GOTO Programs

#include "goto_check.h"

#include "goto_check_c.h"

#include <util/symbol.h>

void goto_check(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const optionst &options,
  message_handlert &message_handler)
{
  const auto &function_symbol = ns.lookup(function_identifier);

  if(function_symbol.mode == ID_C)
  {
    goto_check_c(
      function_identifier, goto_function, ns, options, message_handler);
  }
}

void goto_check(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  goto_check_c(ns, options, goto_functions, message_handler);
}

void goto_check(
  const optionst &options,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  goto_check_c(options, goto_model, message_handler);
}
