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

const char *smt_core_theoryt::equalt::identifier()
{
  return "=";
}

smt_sortt
smt_core_theoryt::equalt::return_sort(const smt_termt &, const smt_termt &)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  INVARIANT(
    lhs.get_sort() == rhs.get_sort(),
    "\"=\" may only be applied to terms which have the same sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::equalt>
  smt_core_theoryt::equal{};

const char *smt_core_theoryt::distinctt::identifier()
{
  return "distinct";
}

smt_sortt
smt_core_theoryt::distinctt::return_sort(const smt_termt &, const smt_termt &)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::distinctt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  INVARIANT(
    lhs.get_sort() == rhs.get_sort(),
    "\"distinct\" may only be applied to terms which have the same sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::distinctt>
  smt_core_theoryt::distinct{};
