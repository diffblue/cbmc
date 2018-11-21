/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_GOTO_INSTRUMENT_GOTO_INSTRUMENT_PARSE_OPTIONS_H
#define CPROVER_GOTO_INSTRUMENT_GOTO_INSTRUMENT_PARSE_OPTIONS_H

#include <ansi-c/ansi_c_language.h>

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_calls_no_body.h>
#include <goto-programs/remove_const_function_pointers.h>
#include <goto-programs/replace_calls.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include <analyses/goto_check.h>

#include "aggressive_slicer.h"
#include "generate_function_bodies.h"

#include "count_eloc.h"

// clang-format off
#define GOTO_INSTRUMENT_OPTIONS \
  "(all)" \
  "(document-claims-latex)(document-claims-html)" \
  "(document-properties-latex)(document-properties-html)" \
  "(dump-c)(dump-cpp)(no-system-headers)(use-all-headers)(dot)(xml)" \
  "(harness)" \
  OPT_GOTO_CHECK \
  /* no-X-check are deprecated and ignored */ \
  "(no-bounds-check)(no-pointer-check)(no-div-by-zero-check)" \
  "(no-nan-check)" \
  "(remove-pointers)" \
  "(no-simplify)" \
  "(assert-to-assume)" \
  "(no-assertions)(no-assumptions)(uninitialized-check)" \
  "(race-check)(scc)(one-event-per-cycle)" \
  "(minimum-interference)" \
  "(mm):(my-events)" \
  "(unwind):(unwindset):(unwindset-file):" \
  "(unwinding-assertions)(partial-loops)(continue-as-loops)" \
  "(log):" \
  "(max-var):(max-po-trans):(ignore-arrays)" \
  "(cfg-kill)(no-dependencies)(force-loop-duplication)" \
  "(call-graph)(reachable-call-graph)" \
  OPT_SHOW_CLASS_HIERARCHY \
  "(no-po-rendering)(render-cluster-file)(render-cluster-function)" \
  "(nondet-volatile)(isr):" \
  "(stack-depth):(nondet-static)" \
  "(function-enter):(function-exit):(branch):" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  "(drop-unused-functions)" \
  "(show-value-sets)" \
  "(show-global-may-alias)" \
  "(show-local-bitvector-analysis)(show-custom-bitvector-analysis)" \
  "(show-escape-analysis)(escape-analysis)" \
  "(custom-bitvector-analysis)" \
  "(show-struct-alignment)(interval-analysis)(show-intervals)" \
  "(show-uninitialized)(show-locations)" \
  "(full-slice)(reachability-slice)(slice-global-inits)" \
  "(fp-reachability-slice):" \
  "(inline)(partial-inline)(function-inline):(log):(no-caching)" \
  OPT_REMOVE_CONST_FUNCTION_POINTERS \
  "(print-internal-representation)" \
  "(remove-function-pointers)" \
  "(show-claims)(property):" \
  "(show-symbol-table)(show-points-to)(show-rw-set)" \
  "(cav11)" \
  OPT_TIMESTAMP \
  "(show-natural-loops)(accelerate)(havoc-loops)" \
  "(error-label):(string-abstraction)" \
  "(verbosity):(version)(xml-ui)(json-ui)(show-loops)" \
  "(accelerate)(constant-propagator)" \
  "(k-induction):(step-case)(base-case)" \
  "(show-call-sequences)(check-call-sequence)" \
  "(interpreter)(show-reaching-definitions)" \
  "(list-symbols)(list-undefined-functions)" \
  "(z3)(add-library)(show-dependence-graph)" \
  "(horn)(skip-loops):(apply-code-contracts)(model-argc-argv):" \
  "(show-threaded)(list-calls-args)" \
  "(undefined-function-is-assume-false)" \
  "(remove-function-body):"\
  OPT_AGGRESSIVE_SLICER \
  OPT_FLUSH \
  "(splice-call):" \
  OPT_REMOVE_CALLS_NO_BODY \
  OPT_REPLACE_FUNCTION_BODY \
  OPT_GOTO_PROGRAM_STATS \
  "(show-local-safe-pointers)(show-safe-dereferences)" \
  OPT_REPLACE_CALLS \
  "(validate-goto-binary)" \
  OPT_VALIDATE \
  OPT_ANSI_C_LANGUAGE \
  // empty last line

// clang-format on

class goto_instrument_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit();
  virtual void help();

  goto_instrument_parse_optionst(int argc, const char **argv):
    parse_options_baset(GOTO_INSTRUMENT_OPTIONS, argc, argv),
    messaget(ui_message_handler),
    ui_message_handler(cmdline, "goto-instrument"),
    function_pointer_removal_done(false),
    partial_inlining_done(false),
    remove_returns_done(false)
  {
  }

protected:
  ui_message_handlert ui_message_handler;
  virtual void register_languages();

  void get_goto_program();
  void instrument_goto_program();

  void do_indirect_call_and_rtti_removal(bool force=false);
  void do_remove_const_function_pointers_only();
  void do_partial_inlining();
  void do_remove_returns();

  bool function_pointer_removal_done;
  bool partial_inlining_done;
  bool remove_returns_done;

  goto_modelt goto_model;

  ui_message_handlert::uit get_ui()
  {
    return ui_message_handler.get_ui();
  }
};

#endif // CPROVER_GOTO_INSTRUMENT_GOTO_INSTRUMENT_PARSE_OPTIONS_H
