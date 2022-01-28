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

#define SMT_BITVECTOR_THEORY_PREDICATE(the_identifier, the_name)               \
  void smt_bit_vector_theoryt::the_name##t::validate(                          \
    const smt_termt &left, const smt_termt &right)                             \
  {                                                                            \
    validate_bit_vector_predicate_arguments(left, right);                      \
  }                                                                            \
                                                                               \
  smt_sortt smt_bit_vector_theoryt::the_name##t::return_sort(                  \
    const smt_termt &, const smt_termt &)                                      \
  {                                                                            \
    return smt_bool_sortt{};                                                   \
  }                                                                            \
                                                                               \
  const char *smt_bit_vector_theoryt::the_name##t::identifier()                \
  {                                                                            \
    return #the_identifier;                                                    \
  }                                                                            \
                                                                               \
  const smt_function_application_termt::factoryt<                              \
    smt_bit_vector_theoryt::the_name##t>                                       \
    smt_bit_vector_theoryt::the_name{};
#include "smt_bit_vector_theory.def"
#undef SMT_BITVECTOR_THEORY_PREDICATE

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
