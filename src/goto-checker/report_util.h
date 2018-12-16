/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_GOTO_CHECKER_REPORT_UTIL_H
#define CPROVER_GOTO_CHECKER_REPORT_UTIL_H

#include "properties.h"

class ui_message_handlert;

void report_success(ui_message_handlert &);
void report_failure(ui_message_handlert &);
void report_inconclusive(ui_message_handlert &);
void report_error(ui_message_handlert &);

void output_properties(
  const propertiest &properties,
  ui_message_handlert &ui_message_handler);

#endif // CPROVER_GOTO_CHECKER_REPORT_UTIL_H
