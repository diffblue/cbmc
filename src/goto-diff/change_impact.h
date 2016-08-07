/*******************************************************************\

Module: Data and control-dependencies of syntactic diff

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_CHANGE_IMPACT_H
#define CPROVER_CHANGE_IMPACT_H

class goto_modelt;

void change_impact(
  const goto_modelt &model_old,
  const goto_modelt &model_new);

#endif
