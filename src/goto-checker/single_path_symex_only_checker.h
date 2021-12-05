/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution only

#ifndef CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_ONLY_CHECKER_H
#define CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_ONLY_CHECKER_H

#include "incremental_goto_checker.h"

#include <goto-symex/path_storage.h>

#include <goto-instrument/unwindset.h>

#include <chrono>

class symex_bmct;

/// Uses goto-symex to generate a `symex_target_equationt` for each path.
class single_path_symex_only_checkert : public incremental_goto_checkert
{
public:
  single_path_symex_only_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;

  virtual ~single_path_symex_only_checkert() = default;

protected:
  abstract_goto_modelt &goto_model;
  symbol_tablet symex_symbol_table;
  namespacet ns;
  guard_managert guard_manager;
  std::unique_ptr<path_storaget> worklist;
  std::chrono::duration<double> symex_runtime;
  unwindsett unwindset;

  void equation_output(
    const symex_bmct &symex,
    const symex_target_equationt &equation);

  virtual void setup_symex(symex_bmct &symex);

  /// Adds the initial goto-symex state as a path to the worklist
  virtual void initialize_worklist();

  /// Continues exploring the given \p path using goto-symex
  /// \return whether the path is ready to be checked
  virtual bool resume_path(path_storaget::patht &path);

  /// Returns whether the given \p path produced by \p symex is ready to be
  /// checked
  virtual bool
  is_ready_to_decide(const symex_bmct &symex, const path_storaget::patht &path);

  /// Returns whether we should stop exploring paths
  virtual bool has_finished_exploration(const propertiest &);

  /// Updates the \p properties from the \p equation and
  /// adds their property IDs to \p updated_properties.
  virtual void update_properties(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties,
    const symex_target_equationt &equation);

  /// Updates the \p properties after having finished exploration and
  /// adds their property IDs to \p updated_properties.
  virtual void final_update_properties(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties);
};

#endif // CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_ONLY_CHECKER_H
