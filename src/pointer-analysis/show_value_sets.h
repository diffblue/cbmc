/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Value Sets

#ifndef CPROVER_POINTER_ANALYSIS_SHOW_VALUE_SETS_H
#define CPROVER_POINTER_ANALYSIS_SHOW_VALUE_SETS_H

#include <util/ui_message.h>
#include "value_set_analysis.h"

class goto_functionst;
class goto_programt;

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis);

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis);

#endif // CPROVER_POINTER_ANALYSIS_SHOW_VALUE_SETS_H
