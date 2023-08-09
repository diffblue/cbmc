// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "goto_inspect_parse_options.h"

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/version.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/show_goto_functions.h>

#include <iostream>

int goto_inspect_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  // Before we do anything else, ensure that a file argument has been given.
  if(cmdline.args.size() != 1)
  {
    help();
    throw invalid_command_line_argument_exceptiont{
      "failed to supply a goto-binary name or an option for inspection",
      "<input goto-binary> <inspection-option>"};
  }

  // This just sets up the defaults (and would interpret options such as --32).
  config.set(cmdline);

  // Normally we would register language front-ends here but as goto-inspect
  // only works on goto binaries, we don't need to

  auto binary_filename = cmdline.args[0];

  // Read goto binary into goto-model
  auto read_goto_binary_result =
    read_goto_binary(binary_filename, ui_message_handler);
  if(!read_goto_binary_result.has_value())
  {
    throw deserialization_exceptiont{
      "failed to read goto program from file '" + binary_filename + "'"};
  }
  auto goto_model = std::move(read_goto_binary_result.value());

  // This has to be called after the defaults are set up (as per the
  // config.set(cmdline) above) otherwise, e.g. the architecture specification
  // will be unknown.
  config.set_from_symbol_table(goto_model.symbol_table);

  if(cmdline.isset("show-goto-functions"))
  {
    show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
    return CPROVER_EXIT_SUCCESS;
  }

  // If an option + binary was provided, the program will have exited
  // gracefully through a different branch. If we hit the code below, it
  // means that something has gone wrong - it's also possible to fall through
  // this case if no optional inspection flag is present in the argument
  // vector. This will ensure that the return value in that case is
  // semantically meaningful, and provide a return value that also satisfies
  // the compiler's requirements based on the signature of `doit()`.
  return CPROVER_EXIT_INCORRECT_TASK;
}

void goto_inspect_parse_optionst::help()
{
  std::cout << '\n'
            << banner_string("Goto-Inspect", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2023") << '\n'
            << align_center_with_border("Diffblue Ltd.") << '\n'
            << align_center_with_border("info@diffblue.com") << '\n';

  std::cout << help_formatter(
    "\n"
    "Usage:                     \tPurpose:\n"
    "\n"
    " {bgoto-inspect} [{y-?}] [{y-h}] [{y--help}] \t show this help\n"
    " {bgoto-inspect} {y--version} \t show version and exit\n"
    " {bgoto-inspect} {y--show-goto-functions} {ufile_name} \t show code for"
    " goto-functions present in goto-binary {ufile_name}\n"
    "\n");
}

goto_inspect_parse_optionst::goto_inspect_parse_optionst(
  int argc,
  const char *argv[])
  : parse_options_baset{
      GOTO_INSPECT_OPTIONS,
      argc,
      argv,
      std::string("GOTO-INSPECT ") + CBMC_VERSION}
{
}
