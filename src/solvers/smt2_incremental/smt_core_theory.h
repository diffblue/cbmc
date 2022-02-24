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

  struct impliest final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<impliest> implies;

  struct andt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<andt> make_and;

  struct ort final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<ort> make_or;

  struct xort final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<xort> make_xor;

  struct equalt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  static const smt_function_application_termt::factoryt<equalt> equal;

  struct distinctt final
  {
    static const char *identifier();
    static smt_sortt return_sort(const smt_termt &lhs, const smt_termt &rhs);
    static void validate(const smt_termt &lhs, const smt_termt &rhs);
  };
  /// Makes applications of the function which returns true iff its two
  /// arguments are not identical.
  static const smt_function_application_termt::factoryt<distinctt> distinct;

  struct if_then_elset final
  {
    static const char *identifier();
    static smt_sortt return_sort(
      const smt_termt &condition,
      const smt_termt &then_term,
      const smt_termt &else_term);
    static void validate(
      const smt_termt &condition,
      const smt_termt &then_term,
      const smt_termt &else_term);
  };
  static const smt_function_application_termt::factoryt<if_then_elset>
    if_then_else;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_CORE_THEORY_H
