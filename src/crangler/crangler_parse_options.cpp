/*******************************************************************\

Module: CRANGLER Command Line Option Processing

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// CRANGLER Command Line Option Processing

#include "crangler_parse_options.h"

#include <util/cout_message.h>
#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/version.h>

#include <json/json_parser.h>

#include "c_wrangler.h"

#include <iostream>

int crangler_parse_optionst::doit()
{
  if(cmdline.args.empty())
  {
    std::cerr << "please give a configuration file\n";
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  for(const auto &file_name : cmdline.args)
    process_crangler_json(file_name);

  return 0;
}

void crangler_parse_optionst::process_crangler_json(
  const std::string &file_name)
{
  console_message_handlert message_handler;
  jsont configuration;

  if(parse_json(file_name, message_handler, configuration))
    return;

  c_wrangler(configuration);
}

void crangler_parse_optionst::help()
{
  std::cout << '\n' << banner_string("CRANGLER", CBMC_VERSION) << '\n';

  std::cout << help_formatter(
    "\n"
    "Usage:                     \tPurpose:\n"
    "\n"
    " {bcrangler} [{y-?}] [{y-h}] [{y--help}] \t show this help\n"
    " {bcrangler} {ufile.json} ... \t configuration file names\n"
    "\n");
}
