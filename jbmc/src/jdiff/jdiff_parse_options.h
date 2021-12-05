/*******************************************************************\

Module: JDIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// JDIFF Command Line Option Processing

#ifndef CPROVER_JDIFF_JDIFF_PARSE_OPTIONS_H
#define CPROVER_JDIFF_JDIFF_PARSE_OPTIONS_H

#include <java_bytecode/goto_check_java.h>

#include <util/parse_options.h>
#include <util/timestamper.h>

#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include <goto-instrument/cover.h>

class goto_modelt;

// clang-format off
#define JDIFF_OPTIONS \
  "(json-ui)" \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  OPT_GOTO_CHECK_JAVA \
  OPT_COVER \
  "(verbosity):(version)" \
  "(no-lazy-methods)" /* should go away */ \
  "(no-refine-strings)" /* should go away */ \
  OPT_TIMESTAMP \
  "u(unified)(change-impact)(forward-impact)(backward-impact)" \
  "(compact-output)"
// clang-format on

class jdiff_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  jdiff_parse_optionst(int argc, const char **argv);

protected:
  void register_languages() override;

  void get_command_line_options(optionst &options);

  bool process_goto_program(const optionst &options, goto_modelt &goto_model);
};

#endif // CPROVER_JDIFF_JDIFF_PARSE_OPTIONS_H
