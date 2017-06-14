/*******************************************************************\

Module: Interval Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interval Analysis

#ifndef CPROVER_ANALYSES_INTERVAL_ANALYSIS_H
#define CPROVER_ANALYSES_INTERVAL_ANALYSIS_H

#include <util/namespace.h>
#include <goto-programs/goto_functions.h>

void interval_analysis(
  const namespacet &ns,
  goto_functionst &goto_functions);

#endif // CPROVER_ANALYSES_INTERVAL_ANALYSIS_H
