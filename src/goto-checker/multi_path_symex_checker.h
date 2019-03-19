/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H

#include <chrono>

#include "fault_localization_provider.h"
#include "goto_symex_property_decider.h"
#include "goto_trace_provider.h"
#include "multi_path_symex_only_checker.h"
#include "witness_provider.h"

/// Performs a multi-path symbolic execution using goto-symex
/// and calls a SAT/SMT solver to check the status of the properties.
class multi_path_symex_checkert : public multi_path_symex_only_checkert,
                                  public goto_trace_providert,
                                  public witness_providert,
                                  public fault_localization_providert
{
public:
  multi_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  /// \copydoc incremental_goto_checkert::operator()(propertiest &properties)
  ///
  /// Note: Repeated invocations of this operator with properties P_1, P_2, ...
  ///   must satisfy the condition 'P_i contains P_i+1'.
  ///   I.e. after checking properties P_i the caller may decide to check
  ///   only a subset of properties P_i+1 in the following invocation,
  ///   but the caller may not add properties to P_i+1 that have not been
  ///   in P_i. Such additional properties will be ignored.
  resultt operator()(propertiest &) override;

  goto_tracet build_full_trace() const override;
  goto_tracet build_shortest_trace() const override;
  goto_tracet build_trace(const irep_idt &) const override;
  const namespacet &get_namespace() const override;

  void output_error_witness(const goto_tracet &) override;
  void output_proof() override;

  fault_location_infot
  localize_fault(const irep_idt &property_id) const override;

protected:
  bool equation_generated;
  goto_symex_property_decidert property_decider;

  /// Prepare the property decider for solving. This sets up the data structures
  /// for tracking goal literals, sets the status of \p properties to be checked
  /// to UNKNOWN and pushes the equation into the solver.
  /// \return the time taken (pushing into the solver is a costly operation)
  virtual std::chrono::duration<double>
  prepare_property_decider(propertiest &properties);

  /// Run the property decider, which calls the SAT solver, and set the status
  /// of checked \p properties accordingly. The property IDs of updated
  /// properties are added to the `result.updated_properties` and the goto
  /// checker's progress (DONE, FOUND_FAIL) is set in \p result.
  /// The \p solver_runtime will be logged.
  virtual void run_property_decider(
    incremental_goto_checkert::resultt &result,
    propertiest &properties,
    std::chrono::duration<double> solver_runtime);
};

#endif // CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
