/******************************************************************\

Module: goto_harness_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#include <cstddef>
#include <iostream>
#include <string>

#include <util/exit_codes.h>
#include <util/version.h>

#include "goto_harness_parse_options.h"

int goto_harness_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  help();
  return CPROVER_EXIT_USAGE_ERROR;
}

void goto_harness_parse_optionst::help()
{
  std::cout << '\n'
            << banner_string("Goto-Harness", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2019") << '\n'
            << align_center_with_border("Diffblue Ltd.") << '\n'
            << align_center_with_border("info@diffblue.com")
            // ^--- No idea if this is the right email address
            << '\n'
            << '\n'
            << "Usage:                       Purpose:\n"
            << '\n'
            << " goto-harness [-?] [-h] [--help]  show help\n"
            << " goto-harness --version           show version\n";
}

goto_harness_parse_optionst::goto_harness_parse_optionst(
  int argc,
  const char *argv[])
  : parse_options_baset{GOTO_HARNESS_OPTIONS, argc, argv}
{
}
