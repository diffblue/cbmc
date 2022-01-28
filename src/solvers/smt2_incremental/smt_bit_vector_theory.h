// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_BIT_VECTOR_THEORY_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_BIT_VECTOR_THEORY_H

#include <solvers/smt2_incremental/smt_terms.h>

class smt_bit_vector_theoryt
{
public:
#define SMT_BITVECTOR_THEORY_PREDICATE(the_identifier, the_name)               \
  /* NOLINTNEXTLINE(readability/identifiers) cpplint does not match the ## */  \
  struct the_name##t final                                                     \
  {                                                                            \
    static const char *identifier();                                           \
    static smt_sortt                                                           \
    return_sort(const smt_termt &left, const smt_termt &right);                \
    static void validate(const smt_termt &left, const smt_termt &right);       \
  };                                                                           \
  static const smt_function_application_termt::factoryt<the_name##t> the_name;
#include "smt_bit_vector_theory.def"
#undef SMT_BITVECTOR_THEORY_PREDICATE

  // Relational operator class declarations
  struct unsigned_less_thant final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<unsigned_less_thant>
    unsigned_less_than;

  struct unsigned_less_than_or_equalt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<
    unsigned_less_than_or_equalt>
    unsigned_less_than_or_equal;

  struct unsigned_greater_thant final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<unsigned_greater_thant>
    unsigned_greater_than;

  struct unsigned_greater_than_or_equalt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<
    unsigned_greater_than_or_equalt>
    unsigned_greater_than_or_equal;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_BIT_VECTOR_THEORY_H
