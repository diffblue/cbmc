/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_CHECKER_H

#include <chrono>

#include <util/optional.h>

#include "goto_symex_property_decider.h"
#include "goto_trace_provider.h"
#include "single_path_symex_only_checker.h"
#include "solver_factory.h"
#include "witness_provider.h"

/// Uses goto-symex to symbolically execute each path in the
/// goto model and calls a solver to find property violations.
class single_path_symex_checkert : public single_path_symex_only_checkert,
                                   public witness_providert,
                                   public goto_trace_providert
{
public:
  single_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;

  goto_tracet build_full_trace() const override;
  goto_tracet build_shortest_trace() const override;
  goto_tracet build_trace(const irep_idt &) const override;
  const namespacet &get_namespace() const override;

  void output_error_witness(const goto_tracet &) override;
  void output_proof() override;

  virtual ~single_path_symex_checkert() = default;

protected:
  bool symex_initialized = false;
  std::unique_ptr<goto_symex_property_decidert> property_decider;

  bool
  is_ready_to_decide(const symex_bmct &, const path_storaget::patht &) override;

  /// Prepare the \p property_decider for solving. This sets up the data
  /// structures for tracking goal literals, sets the status of \p properties to
  /// be checked to UNKNOWN and pushes the equation into the solver.
  /// \return the time taken (pushing into the solver is a costly operation)
  virtual std::chrono::duration<double> prepare_property_decider(
    propertiest &properties,
    symex_target_equationt &equation,
    goto_symex_property_decidert &property_decider);

  /// Run the \p property_decider, which calls the SAT solver, and set the
  /// status of checked \p properties accordingly. The property IDs of updated
  /// properties are added to the `result.updated_properties` and the goto
  /// checker's progress (DONE, FOUND_FAIL) is set in \p result.
  /// The \p solver_runtime will be logged.
  virtual void run_property_decider(
    incremental_goto_checkert::resultt &result,
    propertiest &properties,
    goto_symex_property_decidert &property_decider,
    std::chrono::duration<double> solver_runtime);
};

#endif // CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_CHECKER_H
