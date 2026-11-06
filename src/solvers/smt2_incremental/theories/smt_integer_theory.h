// Author: Michael Tautschnig

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_THEORIES_SMT_INTEGER_THEORY_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_THEORIES_SMT_INTEGER_THEORY_H

#include <solvers/smt2_incremental/ast/smt_terms.h> // NOLINT(build/include)

class smt_integer_theoryt
{
public:
  // Arithmetic operators
  struct negt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &operand);
    static void validate(const smt_termt &operand);
  };
  static const smt_function_application_termt::factoryt<negt> negate;

  struct addt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<addt> add;

  struct subt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<subt> sub;

  struct mult final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<mult> mul;

  // SMT-LIB integer division and modulo. Both follow SMT-LIB's Euclidean
  // semantics (non-negative remainder); callers needing C/truncation semantics
  // (mod_exprt/div_exprt) apply a sign correction.
  struct divt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<divt> divide;

  struct modt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<modt> mod;

  // Comparison operators
  struct less_thant final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<less_thant> less_than;

  struct less_than_or_equalt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<less_than_or_equalt>
    less_than_or_equal;

  struct greater_thant final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<greater_thant>
    greater_than;

  struct greater_than_or_equalt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<greater_than_or_equalt>
    greater_than_or_equal;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_THEORIES_SMT_INTEGER_THEORY_H
