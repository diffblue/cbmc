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

const char *smt_core_theoryt::impliest::identifier()
{
  return "=>";
}

smt_sortt
smt_core_theoryt::impliest::return_sort(const smt_termt &, const smt_termt &)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::impliest::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  INVARIANT(
    lhs.get_sort() == smt_bool_sortt{},
    "Left hand side of \"=>\" must have bool sort.");
  INVARIANT(
    rhs.get_sort() == smt_bool_sortt{},
    "Right hand side of \"=>\" must have bool sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::impliest>
  smt_core_theoryt::implies{};

const char *smt_core_theoryt::andt::identifier()
{
  return "and";
}

smt_sortt
smt_core_theoryt::andt::return_sort(const smt_termt &, const smt_termt &)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::andt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  INVARIANT(
    lhs.get_sort() == smt_bool_sortt{},
    "Left hand side of \"and\" must have bool sort.");
  INVARIANT(
    rhs.get_sort() == smt_bool_sortt{},
    "Right hand side of \"and\" must have bool sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::andt>
  smt_core_theoryt::make_and{};

const char *smt_core_theoryt::ort::identifier()
{
  return "or";
}

smt_sortt
smt_core_theoryt::ort::return_sort(const smt_termt &, const smt_termt &)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::ort::validate(const smt_termt &lhs, const smt_termt &rhs)
{
  INVARIANT(
    lhs.get_sort() == smt_bool_sortt{},
    "Left hand side of \"or\" must have bool sort.");
  INVARIANT(
    rhs.get_sort() == smt_bool_sortt{},
    "Right hand side of \"or\" must have bool sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::ort>
  smt_core_theoryt::make_or{};

const char *smt_core_theoryt::xort::identifier()
{
  return "xor";
}

smt_sortt
smt_core_theoryt::xort::return_sort(const smt_termt &, const smt_termt &)
{
  return smt_bool_sortt{};
}

void smt_core_theoryt::xort::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  INVARIANT(
    lhs.get_sort() == smt_bool_sortt{},
    "Left hand side of \"xor\" must have bool sort.");
  INVARIANT(
    rhs.get_sort() == smt_bool_sortt{},
    "Right hand side of \"xor\" must have bool sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::xort>
  smt_core_theoryt::make_xor{};

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

const char *smt_core_theoryt::if_then_elset::identifier()
{
  return "ite";
}

smt_sortt smt_core_theoryt::if_then_elset::return_sort(
  const smt_termt &,
  const smt_termt &then_term,
  const smt_termt &)
{
  return then_term.get_sort();
}

void smt_core_theoryt::if_then_elset::validate(
  const smt_termt &condition,
  const smt_termt &then_term,
  const smt_termt &else_term)
{
  INVARIANT(
    condition.get_sort() == smt_bool_sortt{},
    "Condition term must have bool sort.");
  INVARIANT(
    then_term.get_sort() == else_term.get_sort(),
    "\"ite\" must have \"then\" and \"else\" terms of the same sort.");
}

const smt_function_application_termt::factoryt<smt_core_theoryt::if_then_elset>
  smt_core_theoryt::if_then_else;
