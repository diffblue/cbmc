/*******************************************************************\

Module: Data and control-dependencies of syntactic diff

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_DIFF_CHANGE_IMPACT_H
#define CPROVER_GOTO_DIFF_CHANGE_IMPACT_H

class goto_modelt;
typedef enum {FORWARD, BACKWARD, BOTH} impact_modet;

void change_impact(
  const goto_modelt &model_old,
  const goto_modelt &model_new,
  impact_modet impact_mode,
  bool compact_output);

#endif // CPROVER_GOTO_DIFF_CHANGE_IMPACT_H
