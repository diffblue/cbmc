/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// GOTO Programs

#include "goto_check.h"

#include <util/options.h>

#include "goto_model.h"
#include "remove_skip.h"

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
