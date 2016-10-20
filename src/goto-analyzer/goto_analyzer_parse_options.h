/*******************************************************************\

Module: Goto-Analyser Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_PARSEOPTIONS_H
#define CPROVER_GOTO_ANALYZER_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>

#include <goto-programs/get_goto_model.h>

class bmct;
class goto_functionst;
class optionst;

#define GOTO_ANALYSER_OPTIONS \
  "(function):" \
  "D:I:(std89)(std99)(std11)" \
  "(classpath):(cp):(main-class):" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  "(show-goto-functions)(show-loops)" \
  "(show-symbol-table)(show-parse-tree)" \
  "(show-properties)(show-reachable-properties)(property):" \
  "(verbosity):(version)" \
  "(gcc)(arch):" \
  "(taint):(show-taint)" \
  "(show-local-may-alias)" \
  "(json):(xml):" \
  "(unreachable-instructions)" \
  "(intervals)(show-intervals)" \
  "(non-null)(show-non-null)"

class goto_analyzer_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  goto_analyzer_parse_optionst(int argc, const char **argv);

protected:
  ui_message_handlert ui_message_handler;
  get_goto_modelt goto_model;

  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);

  virtual bool process_goto_program(const optionst &options);
  bool set_properties();
  
  void eval_verbosity();
  
  bool has_entry_point;
};

#endif
