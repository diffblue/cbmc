/*******************************************************************\

Module: GOTO-DIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Command Line Option Processing

#ifndef CPROVER_GOTO_DIFF_GOTO_DIFF_PARSE_OPTIONS_H
#define CPROVER_GOTO_DIFF_GOTO_DIFF_PARSE_OPTIONS_H

#include <analyses/goto_check_c.h>

#include <util/ui_message.h>
#include <util/parse_options.h>
#include <util/timestamper.h>

#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include <goto-instrument/cover.h>

class goto_modelt;
class optionst;

// clang-format off
#define GOTO_DIFF_OPTIONS \
  "(json-ui)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  "(show-loops)" \
  OPT_GOTO_CHECK \
  OPT_COVER \
  "(verbosity):(version)" \
  OPT_FLUSH \
  OPT_TIMESTAMP \
  "u(unified)(change-impact)(forward-impact)(backward-impact)" \
  "(compact-output)"
// clang-format on

class goto_diff_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_diff_parse_optionst(int argc, const char **argv);

protected:
  void register_languages() override;

  void get_command_line_options(optionst &options);

  bool process_goto_program(const optionst &options, goto_modelt &goto_model);
};

#endif // CPROVER_GOTO_DIFF_GOTO_DIFF_PARSE_OPTIONS_H
