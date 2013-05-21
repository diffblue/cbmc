/*******************************************************************\

Module: Interval Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_INTERVAL_ANALYSIS_H
#define CPROVER_INTERVAL_ANALYSIS_H

#include <util/namespace.h>
#include <goto-programs/goto_functions.h>

void interval_analysis(
  const namespacet &ns,
  goto_functionst &goto_functions);

#endif
