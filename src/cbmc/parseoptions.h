/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_PARSEOPTIONS_H
#define CPROVER_CBMC_PARSEOPTIONS_H

#include <ui_message.h>
#include <parseoptions.h>

#include <langapi/language_ui.h>

#include "xml_interface.h"

class bmct;
class goto_functionst;
class optionst;

#define CBMC_OPTIONS \
  "(program-only)(function):(preprocess)(slice-by-trace):" \
  "(no-simplify)(unwind):(unwindset):(slice-formula)" \
  "(debug-level):(no-propagation)(no-simplify-if)" \
  "(bounds-check)(outfile):(pointer-check)" \
  "(document-subgoals)(all-claims)D:I:(depth):" \
  "(div-by-zero-check)(no-unwinding-assertions)" \
  "(signed-overflow-check)(unsigned-overflow-check)" \
  "(partial-loops)" \
  "(xml-ui)(xml-interface)(vcd):" \
  "(cvc)(smt1)(smt2)(boolector)(yices)(z3)(opensmt)(fpa)" \
  "(no-pretty-names)(beautify-greedy)(beautify-pbs)" \
  "(floatbv)(fixedbv)(no-assertions)(no-assumptions)(nan-check)" \
  "(dimacs)(refine)" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  "(show-goto-functions)(show-value-sets)(show-loops)" \
  "(show-symbol-table)(show-vcc)(show-claims)(claim):" \
  "(error-label):(verbosity):(no-library)" \
  "(version)" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)" \
  "(ppc-macos)(unsigned-char)" \
  "(arrays-uf-always)(arrays-uf-never)" \
  "(string-abstraction)(no-arch)" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  "(decide)" // legacy, and will eventually disappear

class cbmc_parseoptionst:
  public parseoptions_baset,
  public xml_interfacet,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  cbmc_parseoptionst(int argc, const char **argv);
  cbmc_parseoptionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

protected:
  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);
  virtual int do_bmc(bmct &bmc, const goto_functionst &goto_functions);

  virtual bool get_goto_program(
    const optionst &options,
    bmct &bmc,
    goto_functionst &goto_functions);

  virtual bool process_goto_program(
    const optionst &options,
    goto_functionst &goto_functions);
    
  bool set_claims(goto_functionst &goto_functions);
  
  void set_verbosity(messaget &message);
  
  // get any additional stuff before finalizing
  virtual bool get_modules(bmct &bmc)
  {
    return false;
  }
  
  void preprocessing();
};

#endif
