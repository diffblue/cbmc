/*******************************************************************\

Module: Main Module

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Main Module

#include "goto_contracts_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/version.h>

#include <goto-programs/read_goto_binary.h>

#include <iostream>

/// invoke main modules
int goto_contracts_parse_optionst::doit()
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

  get_goto_program();

  // TODO
  // read contracts from file, using Crangler's syntax
  // ASSUME no recursion, function pointers, setjmp/longjmp
  // create a queue of goto models
  // for each element in the queue:
  // reachability slice
  // remove unused functions
  // slice global init
  // compute call graph
  // walk call graph bottom-up
  //   if a function contract exists:
  //     copy goto model, mark function as top-level function
  //     compute assigns set, possibly doing inlining first
  //     replace all calls to this function by contract
  // TODO: loops, dependencies, Makefile, generate contracts stubs,
  // precondition, postcondition

  help();
  return CPROVER_EXIT_USAGE_ERROR;
}

void goto_contracts_parse_optionst::get_goto_program()
{
  log.status() << "Reading GOTO program from '" << cmdline.args[0] << "'"
               << messaget::eom;

  config.set(cmdline);

  auto result = read_goto_binary(cmdline.args[0], ui_message_handler);

  if(!result.has_value())
    throw 0;

  goto_model = std::move(result.value());

  config.set_from_symbol_table(goto_model.symbol_table);
}

/// display command line help
void goto_contracts_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("Goto-contracts", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2021") << '\n'
            << align_center_with_border("Michael Tautschnig") << '\n'
            << align_center_with_border("tautschn@amazon.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-contracts [-?] [-h] [--help]  show help\n"
    " goto-contracts in out              apply contracts\n"
    "\n"
    "Main options:\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    "\n";
  // clang-format on
}
