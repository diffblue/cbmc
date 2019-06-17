/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution for Java

Author: Daniel Kroening, Peter Schrammel

 \*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution for Java

#ifndef CPROVER_JAVA_BYTECODE_JAVA_SINGLE_PATH_SYMEX_CHECKER_H
#define CPROVER_JAVA_BYTECODE_JAVA_SINGLE_PATH_SYMEX_CHECKER_H

#include <goto-checker/bmc_util.h>
#include <goto-checker/counterexample_beautification.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-symex/build_goto_trace.h>

#include "java_bmc_util.h"
#include "java_trace_validation.h"

class java_single_path_symex_checkert : public single_path_symex_checkert
{
public:
  java_single_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : single_path_symex_checkert(options, ui_message_handler, goto_model)
  {
  }

  void setup_symex(symex_bmct &symex) override
  {
    single_path_symex_checkert::setup_symex(symex);
    java_setup_symex(options, goto_model, symex);
  }

  goto_tracet build_full_trace() const override;
  goto_tracet build_shortest_trace() const override;
  goto_tracet build_trace(const irep_idt &property_id) const override;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_SINGLE_PATH_SYMEX_CHECKER_H
