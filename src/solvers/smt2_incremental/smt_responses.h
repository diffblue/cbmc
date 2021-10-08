// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSES_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSES_H

#include <util/irep.h>

class smt_responset : protected irept
{
public:
  // smt_responset does not support the notion of an empty / null state. Use
  // optionalt<smt_responset> instead if an empty response is required.
  smt_responset() = delete;

  using irept::pretty;

protected:
  using irept::irept;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSES_H
