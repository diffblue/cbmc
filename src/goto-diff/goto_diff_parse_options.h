/*******************************************************************\

Module: GOTO-DIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Command Line Option Processing

#ifndef CPROVER_GOTO_DIFF_GOTO_DIFF_PARSE_OPTIONS_H
#define CPROVER_GOTO_DIFF_GOTO_DIFF_PARSE_OPTIONS_H

#include <analyses/goto_check.h>

#include <util/ui_message.h>
#include <util/parse_options.h>
#include <util/timestamper.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include "goto_diff_languages.h"

class goto_modelt;
class optionst;

// clang-format off
#define GOTO_DIFF_OPTIONS \
  "(json-ui)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  OPT_GOTO_CHECK \
  "(cover):" \
  "(verbosity):(version)" \
  OPT_FLUSH \
  OPT_TIMESTAMP \
  "u(unified)(change-impact)(forward-impact)(backward-impact)" \
  "(compact-output)"
// clang-format on

class goto_diff_parse_optionst:
  public parse_options_baset,
  public goto_diff_languagest
{
public:
  virtual int doit();
  virtual void help();

  goto_diff_parse_optionst(int argc, const char **argv);
  goto_diff_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

protected:
  ui_message_handlert ui_message_handler;
  goto_diff_languagest languages2;

  virtual void get_command_line_options(optionst &options);

  virtual int get_goto_program(
    const optionst &options,
    goto_diff_languagest &languages,
    goto_modelt &goto_model);

  virtual bool process_goto_program(
    const optionst &options,
    goto_modelt &goto_model);

  void preprocessing();

  virtual void error_message(const std::string &err) override
  {
    error() << err << eom;
    return;
  }
};

#endif // CPROVER_GOTO_DIFF_GOTO_DIFF_PARSE_OPTIONS_H
