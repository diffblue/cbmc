/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_CHECKER_H

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

  void prepare(
    resultt &result,
    propertiest &properties,
    symex_target_equationt &equation);
  void decide(resultt &result, propertiest &properties);
};

#endif // CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_CHECKER_H
