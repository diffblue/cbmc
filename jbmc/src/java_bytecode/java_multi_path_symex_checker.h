/*******************************************************************\

Module: Goto Checker using Bounded Model Checking for Java

Author: Daniel Kroening, Peter Schrammel

 \*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking for Java

#ifndef CPROVER_JAVA_BYTECODE_JAVA_MULTI_PATH_SYMEX_CHECKER_H
#define CPROVER_JAVA_BYTECODE_JAVA_MULTI_PATH_SYMEX_CHECKER_H

#include <goto-checker/bmc_util.h>
#include <goto-checker/counterexample_beautification.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-symex/build_goto_trace.h>

#include "java_bmc_util.h"

class java_multi_path_symex_checkert : public multi_path_symex_checkert
{
public:
  java_multi_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : multi_path_symex_checkert(options, ui_message_handler, goto_model)
  {
    java_setup_symex(options, goto_model, symex);
  }

  goto_tracet build_full_trace() const override;
  goto_tracet build_trace(const irep_idt &property_id) const override;
  goto_tracet build_shortest_trace() const override;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_MULTI_PATH_SYMEX_CHECKER_H
