/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_PARSEOPTIONS_H
#define CPROVER_GOTO_INSTRUMENT_PARSEOPTIONS_H

#include <ui_message.h>
#include <parseoptions.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>

#define GOTO_INSTRUMENT_OPTIONS \
  "(all)" \
  "(document-claims-latex)(document-claims-html)" \
  "(dump-c)(dump-cpp)(dot)(xml)" \
  "(bounds-check)(no-bounds-check)" \
  "(pointer-check)(no-pointer-check)" \
  "(remove-pointers)" \
  "(leak-check)" \
  "(assert-to-assume)" \
  "(div-by-zero-check)(no-div-by-zero-check)" \
  "(undefined-shift-check)" \
  "(no-assertions)(no-assumptions)(uninitialized-check)" \
  "(nan-check)(no-nan-check)" \
  "(race-check)(scc)(one-event-per-cycle)" \
  "(minimum-interference)" \
  "(mm):(my-events)(unwind):" \
  "(max-var):(max-po-trans):" \
  "(cfg-kill)(no-dependencies)" \
  "(call-graph)" \
  "(no-po-rendering)(render-cluster-file)(render-cluster-function)" \
  "(nondet-volatile)(isr):" \
  "(stack-depth):(nondet-static)" \
  "(function-enter):(function-exit):(branch):" \
  "(signed-overflow-check)(unsigned-overflow-check)" \
  "(show-goto-functions)(show-value-sets)(show-local-may-alias)" \
  "(show-struct-alignment)" \
  "(show-uninitialized)(show-locations)" \
  "(full-slice)(reachability-slice)" \
  "(inline)" \
  "(show-symbol-table)(show-claims)(show-points-to)" \
  "(show-rw-set)(cav11)" \
  "(show-natural-loops)(accelerate)(havoc-loops)" \
  "(error-label):(string-abstraction)" \
  "(verbosity):(version)(xml-ui)(show-loops)" \
  "(accelerate)"

class goto_instrument_parseoptionst:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  goto_instrument_parseoptionst(int argc, const char **argv):
    parseoptions_baset(GOTO_INSTRUMENT_OPTIONS, argc, argv),
    language_uit("goto-instrument", cmdline)
  {
  }
  
protected:
  virtual void register_languages();

  void get_goto_program(
    goto_functionst &goto_functions);

  void instrument_goto_program(
    goto_functionst &goto_functions);
    
  void set_verbosity(messaget &message);
};

#endif
