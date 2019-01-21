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
  std::unique_ptr<path_storaget> worklist;

  void equation_output(
    const symex_bmct &symex,
    const symex_target_equationt &equation);

  virtual void setup_symex(symex_bmct &symex);
};

#endif // CPROVER_GOTO_CHECKER_SINGLE_PATH_SYMEX_ONLY_CHECKER_H
