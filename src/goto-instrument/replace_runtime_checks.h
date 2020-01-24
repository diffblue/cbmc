/*******************************************************************\

Module: Replace Runtime Checks

Author: diffblue

\*******************************************************************/

/// \file
/// Replace Runtime Checks

#ifndef CPROVER_GOTO_INSTRUMENT_REPLACE_RUNTIME_CHECKS_H
#define CPROVER_GOTO_INSTRUMENT_REPLACE_RUNTIME_CHECKS_H

#include <goto-programs/goto_model.h>

class goto_modelt;

void replace_runtime_checks(
  goto_modelt &,
  const std::string &replace_option,
  const std::string &language_id);

#endif // CPROVER_GOTO_INSTRUMENT_REPLACE_RUNTIME_CHECKS_H
