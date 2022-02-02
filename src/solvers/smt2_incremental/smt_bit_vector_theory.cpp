// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_bit_vector_theory.h>

#include <util/invariant.h>

static void validate_bit_vector_predicate_arguments(
  const smt_termt &left,
  const smt_termt &right)
{
  const auto left_sort = left.get_sort().cast<smt_bit_vector_sortt>();
  INVARIANT(left_sort, "Left operand must have bitvector sort.");
  const auto right_sort = right.get_sort().cast<smt_bit_vector_sortt>();
  INVARIANT(right_sort, "Right operand must have bitvector sort.");
  // The below invariant is based on the smtlib standard.
  // See http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
  INVARIANT(
    left_sort->bit_width() == right_sort->bit_width(),
    "Left and right operands must have the same bit width.");
}

// Relational operator definitions

const char *smt_bit_vector_theoryt::unsigned_less_thant::identifier()
{
  return "bvult";
}

smt_sortt smt_bit_vector_theoryt::unsigned_less_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_less_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_less_thant>
  smt_bit_vector_theoryt::unsigned_less_than{};

const char *smt_bit_vector_theoryt::unsigned_less_than_or_equalt::identifier()
{
  return "bvule";
}

smt_sortt smt_bit_vector_theoryt::unsigned_less_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_less_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_less_than_or_equalt>
  smt_bit_vector_theoryt::unsigned_less_than_or_equal{};

const char *smt_bit_vector_theoryt::unsigned_greater_thant::identifier()
{
  return "bvugt";
}

smt_sortt smt_bit_vector_theoryt::unsigned_greater_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_greater_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_greater_thant>
  smt_bit_vector_theoryt::unsigned_greater_than{};

const char *
smt_bit_vector_theoryt::unsigned_greater_than_or_equalt::identifier()
{
  return "bvuge";
}

smt_sortt smt_bit_vector_theoryt::unsigned_greater_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_greater_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_greater_than_or_equalt>
  smt_bit_vector_theoryt::unsigned_greater_than_or_equal{};

const char *smt_bit_vector_theoryt::signed_less_thant::identifier()
{
  return "bvslt";
}

smt_sortt smt_bit_vector_theoryt::signed_less_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_less_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_less_thant>
  smt_bit_vector_theoryt::signed_less_than{};

const char *smt_bit_vector_theoryt::signed_less_than_or_equalt::identifier()
{
  return "bvsle";
}

smt_sortt smt_bit_vector_theoryt::signed_less_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_less_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_less_than_or_equalt>
  smt_bit_vector_theoryt::signed_less_than_or_equal{};

const char *smt_bit_vector_theoryt::signed_greater_thant::identifier()
{
  return "bvsgt";
}

smt_sortt smt_bit_vector_theoryt::signed_greater_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_greater_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_greater_thant>
  smt_bit_vector_theoryt::signed_greater_than{};

const char *smt_bit_vector_theoryt::signed_greater_than_or_equalt::identifier()
{
  return "bvsge";
}

smt_sortt smt_bit_vector_theoryt::signed_greater_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_greater_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_greater_than_or_equalt>
  smt_bit_vector_theoryt::signed_greater_than_or_equal{};

const char *smt_bit_vector_theoryt::addt::identifier()
{
  return "bvadd";
}

smt_sortt smt_bit_vector_theoryt::addt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::addt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::addt>
  smt_bit_vector_theoryt::add{};

const char *smt_bit_vector_theoryt::subtractt::identifier()
{
  return "bvsub";
}

smt_sortt smt_bit_vector_theoryt::subtractt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::subtractt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::subtractt>
  smt_bit_vector_theoryt::subtract{};

const char *smt_bit_vector_theoryt::multiplyt::identifier()
{
  return "bvmul";
}

smt_sortt smt_bit_vector_theoryt::multiplyt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::multiplyt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::multiplyt>
  smt_bit_vector_theoryt::multiply{};

const char *smt_bit_vector_theoryt::unsigned_dividet::identifier()
{
  return "bvudiv";
}

smt_sortt smt_bit_vector_theoryt::unsigned_dividet::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::unsigned_dividet::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_dividet>
  smt_bit_vector_theoryt::unsigned_divide{};

const char *smt_bit_vector_theoryt::signed_dividet::identifier()
{
  return "bvsdiv";
}

smt_sortt smt_bit_vector_theoryt::signed_dividet::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::signed_dividet::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_dividet>
  smt_bit_vector_theoryt::signed_divide{};

const char *smt_bit_vector_theoryt::unsigned_remaindert::identifier()
{
  return "bvurem";
}

smt_sortt smt_bit_vector_theoryt::unsigned_remaindert::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::unsigned_remaindert::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_remaindert>
  smt_bit_vector_theoryt::unsigned_remainder{};

const char *smt_bit_vector_theoryt::signed_remaindert::identifier()
{
  return "bvsrem";
}

smt_sortt smt_bit_vector_theoryt::signed_remaindert::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::signed_remaindert::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_predicate_arguments(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_remaindert>
  smt_bit_vector_theoryt::signed_remainder{};
