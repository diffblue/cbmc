// Author: Michael Tautschnig

#include "smt_integer_theory.h"

#include <util/invariant.h> // NOLINT(build/include)

#include <string>

static void
validate_integer_sort(const std::string &descriptor, const smt_termt &operand)
{
  INVARIANT(
    operand.get_sort().cast<smt_int_sortt>(),
    descriptor + " operand is expected to have an integer sort.");
}

static void validate_integer_sort(const smt_termt &operand)
{
  validate_integer_sort("The", operand);
}

static void validate_integer_sorts(const smt_termt &lhs, const smt_termt &rhs)
{
  validate_integer_sort("Left", lhs);
  validate_integer_sort("Right", rhs);
}

const char *smt_integer_theoryt::negt::identifier()
{
  return "-";
}

smt_sortt smt_integer_theoryt::negt::return_sort(const smt_termt &operand)
{
  return operand.get_sort();
}

void smt_integer_theoryt::negt::validate(const smt_termt &operand)
{
  validate_integer_sort(operand);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::negt>
  smt_integer_theoryt::negate;

const char *smt_integer_theoryt::addt::identifier()
{
  return "+";
}

smt_sortt smt_integer_theoryt::addt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_integer_theoryt::addt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::addt>
  smt_integer_theoryt::add;

const char *smt_integer_theoryt::subt::identifier()
{
  return "-";
}

smt_sortt smt_integer_theoryt::subt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_integer_theoryt::subt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::subt>
  smt_integer_theoryt::sub;

const char *smt_integer_theoryt::mult::identifier()
{
  return "*";
}

smt_sortt smt_integer_theoryt::mult::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_integer_theoryt::mult::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::mult>
  smt_integer_theoryt::mul;

const char *smt_integer_theoryt::divt::identifier()
{
  return "div";
}

smt_sortt smt_integer_theoryt::divt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_integer_theoryt::divt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::divt>
  smt_integer_theoryt::divide;

const char *smt_integer_theoryt::modt::identifier()
{
  return "mod";
}

smt_sortt smt_integer_theoryt::modt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_integer_theoryt::modt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::modt>
  smt_integer_theoryt::mod;

const char *smt_integer_theoryt::less_thant::identifier()
{
  return "<";
}

smt_sortt smt_integer_theoryt::less_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_integer_theoryt::less_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_integer_theoryt::less_thant>
  smt_integer_theoryt::less_than;

const char *smt_integer_theoryt::less_than_or_equalt::identifier()
{
  return "<=";
}

smt_sortt smt_integer_theoryt::less_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_integer_theoryt::less_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_integer_theoryt::less_than_or_equalt>
  smt_integer_theoryt::less_than_or_equal;

const char *smt_integer_theoryt::greater_thant::identifier()
{
  return ">";
}

smt_sortt smt_integer_theoryt::greater_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_integer_theoryt::greater_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_integer_theoryt::greater_thant>
  smt_integer_theoryt::greater_than;

const char *smt_integer_theoryt::greater_than_or_equalt::identifier()
{
  return ">=";
}

smt_sortt smt_integer_theoryt::greater_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_integer_theoryt::greater_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_integer_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_integer_theoryt::greater_than_or_equalt>
  smt_integer_theoryt::greater_than_or_equal;
