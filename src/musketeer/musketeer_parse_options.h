/*******************************************************************\

Module: Command Line Parsing

Author:

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_MUSKETEER_MUSKETEER_PARSE_OPTIONS_H
#define CPROVER_MUSKETEER_MUSKETEER_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>

#define GOTO_FENCE_INSERTER_OPTIONS \
  "(scc)(one-event-per-cycle)(verbosity):" \
  "(mm):(my-events)(unwind):" \
  "(max-var):(max-po-trans):(ignore-arrays)(remove-function-pointers)" \
  "(cfg-kill)(no-dependencies)(force-loop-duplication)(no-loop-duplication)" \
  "(no-po-rendering)(render-cluster-file)(render-cluster-function)" \
  "(cav11)(version)(const-function-pointer-propagation)(print-graph)" \
  "(volatile)(all-shared)(pensieve)(naive)(all-shared-aeg)(async)(userdef)"

class goto_fence_inserter_parse_optionst:
  public parse_options_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  goto_fence_inserter_parse_optionst(int argc, const char **argv):
    parse_options_baset(GOTO_FENCE_INSERTER_OPTIONS, argc, argv),
    language_uit(cmdline, ui_message_handler),
    ui_message_handler(cmdline, "musketeer")
  {
  }

protected:
  ui_message_handlert ui_message_handler;

  virtual void register_languages();

  void get_goto_program(
    goto_functionst &goto_functions);

  void instrument_goto_program(
    goto_functionst &goto_functions);

  void set_verbosity();
};

#endif // CPROVER_MUSKETEER_MUSKETEER_PARSE_OPTIONS_H
