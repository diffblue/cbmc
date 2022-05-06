// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_OBJECT_SIZE_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_OBJECT_SIZE_H

#include <solvers/smt2_incremental/smt_commands.h>
#include <solvers/smt2_incremental/smt_terms.h>

/// Specifics of how the object size lookup is implemented in SMT terms.
/// This uses an uninterpreted function as a lookup. Because these functions
/// must return the same result for a specific input, we can just assert the
/// value of the function output for the inputs where we want to define specific
/// ID input / size output pairs.
struct smt_object_sizet final
{
  smt_object_sizet();
  /// The command for declaring the object size function. The defined function
  /// takes a bit vector encoded unique object identifier and returns
  smt_declare_function_commandt declaration;
  /// Function which makes applications of the smt function.
  using make_applicationt =
    smt_function_application_termt::factoryt<smt_command_functiont>;
  make_applicationt make_application;
  /// Makes the command to define the resulting \p size of calling the object
  /// size function with \p unique_id.
  smt_commandt make_definition(std::size_t unique_id, smt_termt size) const;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_OBJECT_SIZE_H
