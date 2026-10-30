/*******************************************************************\

Module: Process a Goto Program

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "process_goto_program.h"

#include <util/message.h>
#include <util/options.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/elide_cpp_returned_temporaries.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/mm_io.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_cpp_exceptions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/rewrite_rw_ok.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/slice_global_inits.h>
#include <goto-programs/string_abstraction.h>

#include <ansi-c/goto-conversion/goto_check_c.h>
#include <ansi-c/goto-conversion/string_instrumentation.h>

#include "goto_check.h"

bool process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log)
{
  if(options.get_bool_option("string-abstraction"))
    string_instrumentation(goto_model);

  // A C++ virtual table that no reachable code refers to -- the class is
  // never constructed -- need not be initialized.  Initialized, every
  // virtual function in it is an addressed object, and a candidate target of
  // every call through a function pointer of its type: the locale facets
  // that libc++'s <vector> and <functional> declare through <locale>
  // (`extern template class moneypunct_byname<char, false>;') exceeded
  // --object-bits 8 on their own, and their destructors were all candidates
  // of std::function's `__f_->destroy()'.  Before function pointer removal;
  // when string abstraction rewrote the initialization function above,
  // which slicing regenerates, it is skipped.
  if(!options.get_bool_option("string-abstraction"))
    slice_unused_virtual_tables(goto_model, log.get_message_handler());

  // remove function pointers
  log.status() << "Removal of function pointers and virtual functions"
               << messaget::eom;
  remove_function_pointers(log.get_message_handler(), goto_model, false);

  // lower C++ exceptions (CATCH-PUSH/CATCH-POP/THROW) to gotos/assignments so
  // that goto-symex need not model exceptions; no-op if there are none
  remove_cpp_exceptions(goto_model, log.get_message_handler());

  // Construct C++ returned temporaries directly into caller storage
  // (N5008 [class.copy.elis]); must follow function pointer removal.
  elide_cpp_returned_temporaries(goto_model);

  mm_io(goto_model, log.get_message_handler());

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

  if(options.get_bool_option("rewrite-rw-ok"))
    rewrite_rw_ok(goto_model);

  // Drop unused functions before property instrumentation to avoid
  // instrumenting functions that will never be reached. The entry point
  // has been set, and function pointers have already been removed above,
  // so the static call graph is now an accurate reachability oracle.
  if(options.get_bool_option("drop-unused-functions"))
  {
    log.status() << "Removing unused functions" << messaget::eom;
    remove_unused_functions(goto_model, log.get_message_handler());
  }

  // add generic checks
  log.status() << "Generic Property Instrumentation" << messaget::eom;
  goto_check_c(options, goto_model, log.get_message_handler());
  transform_assertions_assumptions(options, goto_model);

  // checks don't know about adjusted float expressions
  adjust_float_expressions(goto_model);

  if(options.get_bool_option("string-abstraction"))
  {
    log.status() << "String Abstraction" << messaget::eom;
    string_abstraction(goto_model, log.get_message_handler());
  }

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  return false;
}
