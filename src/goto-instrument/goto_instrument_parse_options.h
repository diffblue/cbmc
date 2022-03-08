/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_GOTO_INSTRUMENT_GOTO_INSTRUMENT_PARSE_OPTIONS_H
#define CPROVER_GOTO_INSTRUMENT_GOTO_INSTRUMENT_PARSE_OPTIONS_H

#include <util/config.h>
#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/remove_calls_no_body.h>
#include <goto-programs/remove_const_function_pointers.h>
#include <goto-programs/restrict_function_pointers.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/goto_check_c.h>
#include <pointer-analysis/goto_program_dereference.h>

#include "aggressive_slicer.h"
#include "count_eloc.h"
#include "document_properties.h"
#include "dump_c.h"
#include "generate_function_bodies.h"
#include "insert_final_assert_false.h"
#include "nondet_volatile.h"
#include "replace_calls.h"
#include "uninitialized.h"
#include "unwindset.h"

#include "contracts/contracts.h"
#include "wmm/weak_memory.h"

// clang-format off
#define GOTO_INSTRUMENT_OPTIONS \
  OPT_DOCUMENT_PROPERTIES \
  OPT_DUMP_C \
  "(dot)(xml)" \
  OPT_GOTO_CHECK \
  OPT_REMOVE_POINTERS \
  "(no-simplify)" \
  OPT_UNINITIALIZED_CHECK \
  OPT_WMM \
  "(race-check)" \
  OPT_UNWINDSET \
  "(unwindset-file):" \
  "(unwinding-assertions)(partial-loops)(continue-as-loops)" \
  "(log):" \
  "(call-graph)(reachable-call-graph)" \
  OPT_INSERT_FINAL_ASSERT_FALSE \
  OPT_SHOW_CLASS_HIERARCHY \
  "(isr):" \
  "(stack-depth):(nondet-static)" \
  "(nondet-static-exclude):" \
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
  "(value-set-fi-fp-removal)" \
  OPT_REMOVE_CONST_FUNCTION_POINTERS \
  "(print-internal-representation)" \
  "(remove-function-pointers)" \
  "(show-claims)(property):" \
  "(show-symbol-table)(show-points-to)(show-rw-set)" \
  OPT_TIMESTAMP \
  "(show-natural-loops)(show-lexical-loops)(accelerate)(havoc-loops)" \
  "(verbosity):(version)(xml-ui)(json-ui)" \
  "(accelerate)(constant-propagator)" \
  "(k-induction):(step-case)(base-case)" \
  "(show-call-sequences)(check-call-sequence)" \
  "(interpreter)(show-reaching-definitions)" \
  "(list-symbols)(list-undefined-functions)" \
  "(z3)(add-library)(show-dependence-graph)" \
  "(horn)(skip-loops):(model-argc-argv):" \
  "(" FLAG_LOOP_CONTRACTS ")" \
  "(" FLAG_REPLACE_CALL "):" \
  "(" FLAG_ENFORCE_CONTRACT "):" \
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
  "(show-sese-regions)" \
  OPT_REPLACE_CALLS \
  "(validate-goto-binary)" \
  OPT_VALIDATE \
  OPT_ANSI_C_LANGUAGE \
  OPT_RESTRICT_FUNCTION_POINTER \
  OPT_NONDET_VOLATILE \
  "(ensure-one-backedge-per-target)" \
  OPT_CONFIG_LIBRARY \
  // empty last line

// clang-format on

class goto_instrument_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_instrument_parse_optionst(int argc, const char **argv)
    : parse_options_baset(
        GOTO_INSTRUMENT_OPTIONS,
        argc,
        argv,
        "goto-instrument"),
      function_pointer_removal_done(false),
      partial_inlining_done(false),
      remove_returns_done(false)
  {
  }

protected:
  void register_languages() override;

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
};

#endif // CPROVER_GOTO_INSTRUMENT_GOTO_INSTRUMENT_PARSE_OPTIONS_H
