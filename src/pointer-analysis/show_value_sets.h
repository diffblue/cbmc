/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Value Sets

#ifndef CPROVER_POINTER_ANALYSIS_SHOW_VALUE_SETS_H
#define CPROVER_POINTER_ANALYSIS_SHOW_VALUE_SETS_H

#include <pointer-analysis/value_set_analysis.h>
#include <util/ui_message.h>

class goto_modelt;

void show_value_sets(
  ui_message_handlert::uit,
  const goto_modelt &,
  const value_set_analysist &);

#endif // CPROVER_POINTER_ANALYSIS_SHOW_VALUE_SETS_H
