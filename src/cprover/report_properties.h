/*******************************************************************\

Module: Property Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Property Reporting

#ifndef CPROVER_CPROVER_REPORT_PROPERTIES_H
#define CPROVER_CPROVER_REPORT_PROPERTIES_H

#include "solver.h"
#include "solver_types.h" // IWYU pragma: keep

void report_properties(const std::vector<propertyt> &);

solver_resultt overall_outcome(const std::vector<propertyt> &);

#endif // CPROVER_CPROVER_REPORT_PROPERTIES_H
