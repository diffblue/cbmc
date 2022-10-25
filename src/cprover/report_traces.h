/*******************************************************************\

Module: Report Traces

Author: Daniel Kroening <dkr@amazon.com>

\*******************************************************************/

/// \file
/// Report Traces

#ifndef CPROVER_CPROVER_REPORT_TRACES_H
#define CPROVER_CPROVER_REPORT_TRACES_H

#include "solver_types.h" // IWYU pragma: keep

void report_traces(
  const std::vector<framet> &frames,
  const std::vector<propertyt> &properties,
  bool verbose,
  const namespacet &);

#endif // CPROVER_CPROVER_REPORT_TRACES_H
