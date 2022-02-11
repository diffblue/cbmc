/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// GOTO Programs

#include "goto_check.h"

#include <util/options.h>
#include <util/symbol.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <ansi-c/goto_check_c.h>

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

static void transform_assertions_assumptions(
  goto_programt &goto_program,
  bool enable_assertions,
  bool enable_built_in_assertions,
  bool enable_assumptions)
{
  bool did_something = false;

  for(auto &instruction : goto_program.instructions)
  {
    if(instruction.is_assert())
    {
      bool is_user_provided =
        instruction.source_location().get_bool("user-provided");

      if(
        (is_user_provided && !enable_assertions &&
         instruction.source_location().get_property_class() != "error label") ||
        (!is_user_provided && !enable_built_in_assertions))
      {
        instruction.turn_into_skip();
        did_something = true;
      }
    }
    else if(instruction.is_assume())
    {
      if(!enable_assumptions)
      {
        instruction.turn_into_skip();
        did_something = true;
      }
    }
  }

  if(did_something)
    remove_skip(goto_program);
}

void transform_assertions_assumptions(
  const optionst &options,
  goto_modelt &goto_model)
{
  const bool enable_assertions = options.get_bool_option("assertions");
  const bool enable_built_in_assertions =
    options.get_bool_option("built-in-assertions");
  const bool enable_assumptions = options.get_bool_option("assumptions");

  // check whether there could possibly be anything to do
  if(enable_assertions && enable_built_in_assertions && enable_assumptions)
    return;

  for(auto &entry : goto_model.goto_functions.function_map)
  {
    transform_assertions_assumptions(
      entry.second.body,
      enable_assertions,
      enable_built_in_assertions,
      enable_assumptions);
  }
}

void transform_assertions_assumptions(
  const optionst &options,
  goto_programt &goto_program)
{
  const bool enable_assertions = options.get_bool_option("assertions");
  const bool enable_built_in_assertions =
    options.get_bool_option("built-in-assertions");
  const bool enable_assumptions = options.get_bool_option("assumptions");

  // check whether there could possibly be anything to do
  if(enable_assertions && enable_built_in_assertions && enable_assumptions)
    return;

  transform_assertions_assumptions(
    goto_program,
    enable_assertions,
    enable_built_in_assertions,
    enable_assumptions);
}
