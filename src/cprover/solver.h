/*******************************************************************\

Module: Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Equality Propagation

#ifndef CPROVER_CPROVER_SOLVER_H
#define CPROVER_CPROVER_SOLVER_H

#include <util/expr.h>

enum class solver_resultt
{
  ALL_PASS,
  SOME_FAIL,
  ERROR
};

class solver_optionst
{
public:
  bool trace;
  bool verbose;
  std::size_t loop_limit;
};

solver_resultt
solver(const std::vector<exprt> &, const solver_optionst &, const namespacet &);

#endif // CPROVER_CPROVER_SOLVER_H
