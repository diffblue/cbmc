/*******************************************************************\

Module: Solver Progress Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver Progress Reporting

#ifndef CPROVER_CPROVER_SOLVER_PROGRESS_H
#define CPROVER_CPROVER_SOLVER_PROGRESS_H

#include "solver_types.h"

class solver_progresst
{
public:
  solver_progresst(std::size_t __total, bool __verbose)
    : total(__total), verbose(__verbose)
  {
  }

  void operator()(std::size_t current);
  void finished();

private:
  bool first = true;
  std::size_t total = 0;
  bool verbose;
};

#endif // CPROVER_CPROVER_SOLVER_PROGRESS_H
