/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CLOBBER_CLOBBER_PARSE_OPTIONS_H
#define CPROVER_CLOBBER_CLOBBER_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>

#include <analyses/goto_check.h>
#include <goto-programs/show_goto_functions.h>

class goto_functionst;
class optionst;

#define CLOBBER_OPTIONS \
  "(depth):(context-bound):(unwind):" \
  GOTO_CHECK_OPTIONS \
  OPT_SHOW_GOTO_FUNCTIONS \
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
  ui_message_handlert ui_message_handler;

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

#endif // CPROVER_CLOBBER_CLOBBER_PARSE_OPTIONS_H
