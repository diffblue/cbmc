/*******************************************************************\

Module: Process a Goto Program

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "process_goto_program.h"

#include <analyses/goto_check.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/mm_io.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>

#include <util/message.h>
#include <util/options.h>

bool process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log)
{
  if(options.get_bool_option("string-abstraction"))
    string_instrumentation(goto_model);

  // remove function pointers
  log.status() << "Removal of function pointers and virtual functions"
               << messaget::eom;
  remove_function_pointers(
    log.get_message_handler(),
    goto_model,
    options.get_bool_option("pointer-check"));

  mm_io(goto_model);

  // instrument library preconditions
  instrument_preconditions(goto_model);

  // do partial inlining
  if(options.get_bool_option("partial-inline"))
  {
    log.status() << "Partial Inlining" << messaget::eom;
    goto_partial_inline(goto_model, log.get_message_handler());
  }

  // remove returns, gcc vectors, complex
  if(
    options.get_bool_option("remove-returns") ||
    options.get_bool_option("string-abstraction"))
  {
    remove_returns(goto_model);
  }

  remove_vector(goto_model);
  remove_complex(goto_model);

  if(options.get_bool_option("rewrite-union"))
    rewrite_union(goto_model);

  // add generic checks
  log.status() << "Generic Property Instrumentation" << messaget::eom;
  goto_check(options, goto_model, log.get_message_handler());

  // checks don't know about adjusted float expressions
  adjust_float_expressions(goto_model);

  if(options.get_bool_option("string-abstraction"))
  {
    log.status() << "String Abstraction" << messaget::eom;
    string_abstraction(goto_model, log.get_message_handler());
  }

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // add loop ids
  goto_model.goto_functions.compute_loop_numbers();

  return false;
}
