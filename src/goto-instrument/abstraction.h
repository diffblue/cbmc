/*******************************************************************\

Module: Abstraction

Author: Lefan Zhang, lefanz@amazon.com
        Murali Talupur talupur@amazon.com

\*******************************************************************/

/// \file
/// Abstraction
/// Abstract certain data types to make proofs unbounded

#ifndef CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H
#define CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H

#include <util/expr.h>
#include <util/json.h>

#include <goto-programs/goto_model.h>
#include <util/ui_message.h>
#include <util/options.h>

#include "abstraction_spect.h"

class am_abstractiont
{
public:
  // link abst functions to goto programs
  static void link_abst_functions(goto_modelt &goto_model, const abstraction_spect &abst_spec, ui_message_handlert &msg_handler, const optionst &options);

  // abstract goto programs
  static void abstract_goto_program(goto_modelt &goto_model, abstraction_spect &abst_spec);

};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H
