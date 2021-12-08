/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H

#include "incremental_goto_checker.h"

#include <goto-symex/path_storage.h>

#include <goto-instrument/unwindset.h>

#include "symex_bmc.h"

class multi_path_symex_only_checkert : public incremental_goto_checkert
{
public:
  multi_path_symex_only_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;

protected:
  abstract_goto_modelt &goto_model;
  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  guard_managert guard_manager;
  path_fifot path_storage; // should go away
  unwindsett unwindset;
  symex_bmct symex;

  /// Generates the equation by running goto-symex
  virtual void generate_equation();

  /// Updates the \p properties from the `equation` and
  /// adds their property IDs to \p updated_properties.
  virtual void update_properties(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties);
};

#endif // CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H
