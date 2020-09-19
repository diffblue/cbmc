/*******************************************************************\

Module: Rr_abstraction

Author: Lefan Zhang, lefanz@amazon.com
        Murali Talupur talupur@amazon.com

\*******************************************************************/

/// \file
/// Abstraction
/// Abstract certain data types to make proofs unbounded

#include <iostream>
#include <queue>

#include "rr_abstraction.h"
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_goto_model.h>
#include <linking/static_lifetime_init.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

void rr_abstractiont::link_abst_functions(
  goto_modelt &goto_model,
  const rr_abstraction_spect &abst_spec,
  ui_message_handlert &msg_handler,
  const optionst &options)
{
  std::vector<std::string> abstfiles =
    abst_spec.get_abstraction_function_files(); // get abst function file names
  goto_modelt goto_model_for_abst_fns =
    initialize_goto_model(abstfiles, msg_handler, options); // read files
  link_goto_model(
    goto_model, goto_model_for_abst_fns, msg_handler); // link goto model
}

void rr_abstractiont::abstract_goto_program(
  goto_modelt &goto_model,
  rr_abstraction_spect &abst_spec)
{
  return;
}
