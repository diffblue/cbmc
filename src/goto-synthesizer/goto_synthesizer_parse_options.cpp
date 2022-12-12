/*******************************************************************\
Module: Parse Options Module
Author: Qinheping Hu
\*******************************************************************/

/// \file
/// Main Module

#include "goto_synthesizer_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/version.h>

#include <goto-programs/read_goto_binary.h>

#include <iostream>

/// invoke main modules
int goto_synthesizer_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.args.size() != 1 && cmdline.args.size() != 2)
  {
    help();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  register_languages();

  const auto result_get_goto_program = get_goto_program();
  if(result_get_goto_program != CPROVER_EXIT_SUCCESS)
    return result_get_goto_program;

  // TODO
  // Migrate synthesizer and tests from goto-instrument to goto-synthesizer

  help();
  return CPROVER_EXIT_USAGE_ERROR;
}

int goto_synthesizer_parse_optionst::get_goto_program()
{
  log.status() << "Reading GOTO program from '" << cmdline.args[0] << "'"
               << messaget::eom;

  config.set(cmdline);

  auto result = read_goto_binary(cmdline.args[0], ui_message_handler);

  if(!result.has_value())
    return CPROVER_EXIT_USAGE_ERROR;

  goto_model = std::move(result.value());

  config.set_from_symbol_table(goto_model.symbol_table);
  return CPROVER_EXIT_SUCCESS;
}

/// display command line help
void goto_synthesizer_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("Goto-synthesizer", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2022") << '\n'
            << align_center_with_border("Qinheping Hu") << '\n'
            << align_center_with_border("qinhh@amazon.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-synthesizer [-?] [-h] [--help]  show help\n"
    " goto-synthesizer in out              synthesize and apply loop invariants.\n" // NOLINT(*)
    "\n"
    "Main options:\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    " --verbosity #                verbosity level\n"
    "\n";
  // clang-format on
}
