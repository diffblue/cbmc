/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYMEX_PARSE_OPTIONS_H
#define CPROVER_SYMEX_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <goto-programs/get_goto_model.h>

#include <langapi/language_ui.h>

#include "path_search.h"

class goto_functionst;
class optionst;

#define SYMEX_OPTIONS \
  "(function):" \
  "D:I:" \
  "(depth):(context-bound):(branch-bound):(unwind):" \
  "(bounds-check)(pointer-check)(div-by-zero-check)(memory-leak-check)" \
  "(signed-overflow-check)(unsigned-overflow-check)(nan-check)" \
  "(float-overflow-check)" \
  "(no-assertions)(no-assumptions)" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  "(error-label):(verbosity):(no-library)" \
  "(version)" \
  "(bfs)(dfs)(locs)" \
  "(cover):" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(string-abstraction)(no-arch)(arch):(floatbv)(fixedbv)" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  "(show-locs)(show-vcc)(show-properties)(show-goto-functions)" \
  "(property):(trace)(show-trace)(stop-on-fail)(eager-infeasibility)" \
  "(no-simplify)(no-unwinding-assertions)(no-propagation)"
  // the last line is for CBMC-regression testing only

class symex_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  symex_parse_optionst(int argc, const char **argv);

protected:
  ui_message_handlert ui_message_handler;
  get_goto_modelt goto_model;

  void get_command_line_options(optionst &options);
  bool process_goto_program(const optionst &options);
  bool set_properties();

  void report_success();
  void report_failure();
  void report_properties(const path_searcht::property_mapt &);
  void report_cover(const path_searcht::property_mapt &);
  void show_counterexample(const class goto_tracet &);
            
  void eval_verbosity();

  std::string get_test(const goto_tracet &goto_trace);
};

#endif
