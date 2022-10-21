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

class inductiveness_resultt
{
public:
  enum outcomet
  {
    INDUCTIVE,
    BASE_CASE_FAIL,
    STEP_CASE_FAIL
  } outcome;

  static inductiveness_resultt inductive()
  {
    return inductiveness_resultt(INDUCTIVE);
  }

  static inductiveness_resultt base_case_fail(workt refuted)
  {
    auto result = inductiveness_resultt(BASE_CASE_FAIL);
    result.work = std::move(refuted);
    return result;
  }

  static inductiveness_resultt step_case_fail(workt dropped)
  {
    auto result = inductiveness_resultt(STEP_CASE_FAIL);
    result.work = std::move(dropped);
    return result;
  }

  optionalt<workt> work;

private:
  explicit inductiveness_resultt(outcomet __outcome) : outcome(__outcome)
  {
  }
};

inductiveness_resultt inductiveness_check(
  std::vector<framet> &frames,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const solver_optionst &,
  const namespacet &,
  std::vector<propertyt> &properties,
  std::size_t property_index);

#endif // CPROVER_CPROVER_INDUCTIVENESS_H
