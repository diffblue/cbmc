/*******************************************************************\

Module: Inductiveness

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Inductiveness

#ifndef CPROVER_CPROVER_INDUCTIVENESS_H
#define CPROVER_CPROVER_INDUCTIVENESS_H

#include "solver_types.h"

class solver_optionst;

enum inductiveness_resultt
{
  INDUCTIVE,
  BASE_CASE_FAIL,
  STEP_CASE_FAIL
};

inductiveness_resultt inductiveness_check(
  std::vector<framet> &frames,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const solver_optionst &,
  const namespacet &,
  std::vector<propertyt> &properties,
  std::size_t property_index);

#endif // CPROVER_CPROVER_INDUCTIVENESS_H
