/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CLOBBER_PARSEOPTIONS_H
#define CPROVER_CLOBBER_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>

class goto_functionst;
class optionst;

#define CLOBBER_OPTIONS \
  "(depth):(context-bound):(unwind):" \
  "(bounds-check)(pointer-check)(div-by-zero-check)(memory-leak-check)" \
  "(signed-overflow-check)(unsigned-overflow-check)(nan-check)" \
  "(float-overflow-check)" \
  "(no-assertions)(no-assumptions)" \
  "(error-label):(verbosity):(no-library)" \
  "(version)" \
  "(string-abstraction)" \
  "(show-locs)(show-vcc)(show-properties)(show-trace)" \
  "(property):"

class clobber_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  clobber_parse_optionst(int argc, const char **argv);
  clobber_parse_optionst(
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
  void show_counterexample(const class goto_tracet &);
            
  void eval_verbosity();
};

#endif
