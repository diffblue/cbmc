/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYMEX_PARSEOPTIONS_H
#define CPROVER_SYMEX_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parseoptions.h>

#include <langapi/language_ui.h>

class goto_functionst;
class optionst;

#define SYMEX_OPTIONS \
  "(function):" \
  "D:I:" \
  "(depth):(context-bound):" \
  "(bounds-check)(pointer-check)(div-by-zero-check)(memory-leak-check)" \
  "(signed-overflow-check)(unsigned-overflow-check)(nan-check)" \
  "(no-assertions)(no-assumptions)" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  "(error-label):(verbosity):(no-library)" \
  "(version)" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(string-abstraction)(no-arch)(arch):" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  "(show-locs)(show-vcc)(show-properties)" \
  "(property):"

class symex_parseoptionst:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  symex_parseoptionst(int argc, const char **argv);
  symex_parseoptionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

protected:
  void get_command_line_options(optionst &options);

  bool get_goto_program(
    const optionst &options,
    goto_functionst &goto_functions);

  bool process_goto_program(
    const optionst &options,
    goto_functionst &goto_functions);
    
  bool set_properties(goto_functionst &goto_functions);

  void report_success();
  void report_failure();
  void show_counterexample(const class safety_checkert &);
            
  void eval_verbosity();
};

#endif
