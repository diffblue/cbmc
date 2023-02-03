// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_IS_DYNAMIC_OBJECT_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_IS_DYNAMIC_OBJECT_H

#include <solvers/smt2_incremental/ast/smt_commands.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>

/// Specifics of how the dynamic object status lookup is implemented in SMT
/// terms. This uses an uninterpreted function as a lookup. Because these
/// functions must return the same result for a specific input, we can just
/// assert the value of the function output for the inputs where we want to
/// define specific ID input / dynamic_object output pairs.
struct smt_is_dynamic_objectt final
{
  smt_is_dynamic_objectt();
  /// The command for declaring the is_dynamic_object function. The defined
  /// function takes a bit vector encoded unique object identifier and returns
  /// a boolean value.
  smt_declare_function_commandt declaration;
  /// Function which makes applications of the smt function.
  using make_applicationt =
    smt_function_application_termt::factoryt<smt_command_functiont>;
  make_applicationt make_application;
  /// Makes the command to define the resulting \p is_dynamic_object status for
  /// calls to the `is_dynamic_object` function with \p unique_id.
  smt_commandt
  make_definition(std::size_t unique_id, bool is_dynamic_object) const;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_IS_DYNAMIC_OBJECT_H
