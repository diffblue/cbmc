// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_core_theory.h>

const char *smt_core_theoryt::nott::identifier()
{
  return "not";
}

smt_sortt smt_core_theoryt::nott::return_sort(const smt_termt &operand)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::nott::validate(const smt_termt &operand)
{
  INVARIANT(
    operand.get_sort() == smt_bool_sortt{},
    "\"not\" may only be applied to terms which have bool sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::nott>
  smt_core_theoryt::make_not{};
