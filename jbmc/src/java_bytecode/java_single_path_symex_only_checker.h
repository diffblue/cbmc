/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution for Java

Author: Daniel Kroening, Peter Schrammel

 \*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution for Java

#ifndef CPROVER_JAVA_BYTECODE_JAVA_SINGLE_PATH_SYMEX_ONLY_CHECKER_H
#define CPROVER_JAVA_BYTECODE_JAVA_SINGLE_PATH_SYMEX_ONLY_CHECKER_H

#include <goto-checker/single_path_symex_only_checker.h>

#include "java_bmc_util.h"

class java_single_path_symex_only_checkert
  : public single_path_symex_only_checkert
{
public:
  java_single_path_symex_only_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : single_path_symex_only_checkert(options, ui_message_handler, goto_model)
  {
  }

  void setup_symex(symex_bmct &symex) override
  {
    single_path_symex_only_checkert::setup_symex(symex);
    java_setup_symex(options, goto_model, symex);
  }
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_SINGLE_PATH_SYMEX_ONLY_CHECKER_H
