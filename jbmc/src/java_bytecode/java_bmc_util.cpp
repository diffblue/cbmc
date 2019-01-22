/*******************************************************************\

Module: Bounded Model Checking Utils for Java

Author: Daniel Kroening, Peter Schrammel

 \*******************************************************************/

/// \file
/// Bounded Model Checking Utils for Java

#include "java_bmc_util.h"

#include <goto-checker/symex_bmc.h>
#include <goto-programs/abstract_goto_model.h>
#include <java_bytecode/java_enum_static_init_unwind_handler.h>

void java_setup_symex(
  const optionst &options,
  abstract_goto_modelt &goto_model,
  symex_bmct &symex)
{
  // unwinds <clinit> loops to number of enum elements
  if(options.get_bool_option("java-unwind-enum-static"))
  {
    // clang-format off
    // (it asks for the body to be at the same indent level as the parameters
    //  for some reason)
    symex.add_loop_unwind_handler(
      [&goto_model](
        const goto_symex_statet::call_stackt &context,
        unsigned loop_num,
        unsigned unwind,
        unsigned &max_unwind)
      { // NOLINT (*)
        return java_enum_static_init_unwind_handler(
          context, loop_num, unwind, max_unwind, goto_model.get_symbol_table());
      });
    // clang-format on
  }
}
