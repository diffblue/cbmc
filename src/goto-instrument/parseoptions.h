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
  "(dump-c)" \
  "(bounds-check)(no-bounds-check)" \
  "(pointer-check)(no-pointer-check)" \
  "(remove-pointers)" \
  "(leak-check)" \
  "(assert-to-assume)" \
  "(div-by-zero-check)(no-div-by-zero-check)" \
  "(no-assertions)(no-assumptions)(uninitialized-check)" \
  "(nan-check)(no-nan-check)" \
  "(race-check)(tso)(rmo)" \
  "(nondet-volatile)(isr):" \
  "(stack-depth):(nondet-static)" \
  "(signed-overflow-check)(unsigned-overflow-check)" \
  "(show-goto-functions)(show-value-sets)" \
  "(show-struct-alignment)" \
  "(show-uninitialized)(show-locations)" \
  "(full-slice)(reachability-slice)" \
  "(show-symbol-table)(show-claims)(show-points-to)" \
  "(error-label):(string-abstraction)" \
  "(verbosity):(version)(xml-ui)"

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
