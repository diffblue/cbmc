/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_PARSEOPTIONS_H
#define CPROVER_GOTO_INSTRUMENT_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>

#define GOTO_INSTRUMENT_OPTIONS \
  "(all)" \
  "(document-claims-latex)(document-claims-html)" \
  "(document-properties-latex)(document-properties-html)" \
  "(dump-c)(dump-cpp)(use-system-headers)(dot)(xml)" \
  "(bounds-check)(no-bounds-check)" \
  "(pointer-check)(memory-leak-check)(no-pointer-check)" \
  "(remove-pointers)" \
  "(no-simplify)" \
  "(assert-to-assume)" \
  "(div-by-zero-check)(no-div-by-zero-check)" \
  "(undefined-shift-check)" \
  "(no-assertions)(no-assumptions)(uninitialized-check)" \
  "(nan-check)(no-nan-check)" \
  "(race-check)(scc)(one-event-per-cycle)" \
  "(minimum-interference)" \
  "(mm):(my-events)(unwind):" \
  "(max-var):(max-po-trans):(ignore-arrays)" \
  "(cfg-kill)(no-dependencies)(force-loop-duplication)" \
  "(call-graph)" \
  "(no-po-rendering)(render-cluster-file)(render-cluster-function)" \
  "(nondet-volatile)(isr):" \
  "(stack-depth):(nondet-static)" \
  "(function-enter):(function-exit):(branch):" \
  "(signed-overflow-check)(unsigned-overflow-check)(float-overflow-check)" \
  "(show-goto-functions)(show-value-sets)(show-local-may-alias)" \
  "(show-local-bitvector-analysis)" \
  "(show-struct-alignment)(interval-analysis)(show-intervals)" \
  "(show-uninitialized)(show-locations)" \
  "(full-slice)(reachability-slice)" \
  "(inline)" \
  "(show-claims)(show-properties)" \
  "(show-symbol-table)(show-points-to)(show-rw-set)" \
  "(cav11)" \
  "(show-natural-loops)(accelerate)(havoc-loops)" \
  "(error-label):(string-abstraction)" \
  "(verbosity):(version)(xml-ui)(show-loops)" \
  "(accelerate)" \
  "(k-induction):(step-case)(base-case)" \
  "(show-call-sequences)(check-call-sequence)" \
  "(interpreter)(show-reaching-definitions)(count-eloc)" \
  "(list-symbols)(list-undefined-functions)" \
  "(z3)(add-library)"

class goto_instrument_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  goto_instrument_parse_optionst(int argc, const char **argv):
    parse_options_baset(GOTO_INSTRUMENT_OPTIONS, argc, argv),
    language_uit("goto-instrument", cmdline)
  {
  }
  
protected:
  virtual void register_languages();

  void get_goto_program(
    goto_functionst &goto_functions);

  void instrument_goto_program(
    goto_functionst &goto_functions);
    
  void eval_verbosity();
};

#endif
