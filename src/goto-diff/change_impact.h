/*******************************************************************\

Module: Data and control-dependencies of syntactic diff

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Data and control-dependencies of syntactic diff

#ifndef CPROVER_GOTO_DIFF_CHANGE_IMPACT_H
#define CPROVER_GOTO_DIFF_CHANGE_IMPACT_H

class goto_modelt;
enum class impact_modet { FORWARD, BACKWARD, BOTH };

void change_impact(
  const goto_modelt &model_old,
  const goto_modelt &model_new,
  impact_modet impact_mode,
  bool compact_output);

#endif // CPROVER_GOTO_DIFF_CHANGE_IMPACT_H
