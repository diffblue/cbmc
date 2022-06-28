// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_ARRAY_THEORY_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_ARRAY_THEORY_H

#include <solvers/smt2_incremental/smt_terms.h>

class smt_array_theoryt
{
public:
  struct selectt final
  {
    static const char *identifier();
    static smt_sortt
    return_sort(const smt_termt &array, const smt_termt &index);
    static void validate(const smt_termt &array, const smt_termt &index);
  };
  static const smt_function_application_termt::factoryt<selectt> select;

  struct storet final
  {
    static const char *identifier();
    static smt_sortt return_sort(
      const smt_termt &array,
      const smt_termt &index,
      const smt_termt &value);
    static void validate(
      const smt_termt &array,
      const smt_termt &index,
      const smt_termt &value);
  };
  static const smt_function_application_termt::factoryt<storet> store;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_ARRAY_THEORY_H
