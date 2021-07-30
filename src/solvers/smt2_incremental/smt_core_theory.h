// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_CORE_THEORY_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_CORE_THEORY_H

#include <solvers/smt2_incremental/smt_terms.h>

class smt_core_theoryt
{
public:
  struct nott final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &operand);
    static void validate(const smt_termt &operand);
  };
  static const smt_function_application_termt::factoryt<nott> make_not;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_CORE_THEORY_H
