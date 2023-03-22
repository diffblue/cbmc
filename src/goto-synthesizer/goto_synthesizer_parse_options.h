/*******************************************************************\
Module: Command Line Parsing
Author: Qinheping Hu
\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H
#define CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H

#include <util/config.h>
#include <util/options.h>
#include <util/parse_options.h>

#include <goto-programs/goto_model.h>

#include <goto-checker/solver_factory.h>
#include <goto-instrument/contracts/contracts.h>

#include "dump_loop_contracts.h"

// clang-format off
#define GOTO_SYNTHESIZER_OPTIONS \
  OPT_DUMP_LOOP_CONTRACTS \
  "(" FLAG_LOOP_CONTRACTS_NO_UNWIND ")" \
  OPT_CONFIG_BACKEND \
  OPT_SOLVER \
  "(verbosity):(version)(xml-ui)(json-ui)" \
  // empty last line

// clang-format on

class goto_synthesizer_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_synthesizer_parse_optionst(int argc, const char **argv)
    : parse_options_baset(
        GOTO_SYNTHESIZER_OPTIONS,
        argc,
        argv,
        "goto-synthesizer")
  {
  }

protected:
  void register_languages() override;

  int get_goto_program();

  // Get the options same as using CBMC api without any flags and set any
  // options specified in the command line.
  optionst get_options();

  goto_modelt goto_model;
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H
