/*******************************************************************\

Module: Goto Checker using Bounded Model Checking for Java

Author: Daniel Kroening, Peter Schrammel

 \*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking for Java

#ifndef CPROVER_JAVA_BYTECODE_JAVA_MULTI_PATH_SYMEX_ONLY_CHECKER_H
#define CPROVER_JAVA_BYTECODE_JAVA_MULTI_PATH_SYMEX_ONLY_CHECKER_H

#include <goto-checker/multi_path_symex_only_checker.h>

#include "java_bmc_util.h"

class java_multi_path_symex_only_checkert
  : public multi_path_symex_only_checkert
{
public:
  java_multi_path_symex_only_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : multi_path_symex_only_checkert(options, ui_message_handler, goto_model)
  {
    java_setup_symex(options, goto_model, symex);
  }
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_MULTI_PATH_SYMEX_ONLY_CHECKER_H
