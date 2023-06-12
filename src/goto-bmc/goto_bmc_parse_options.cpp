// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "goto_bmc_parse_options.h"

#include <util/exit_codes.h>
#include <util/message.h>
#include <util/version.h>

#include <libcprover-cpp/api_options.h>
#include <libcprover-cpp/verification_result.h>

#include "api.h"

goto_bmc_parse_optionst::goto_bmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      GOTO_BMC_OPTIONS,
      argc,
      argv,
      std::string("goto-bmc") + CBMC_VERSION)
{
}

void print_messages_to_stdout(
  const api_messaget &message,
  api_call_back_contextt api_call_back_context)
{
  const messaget *log = static_cast<messaget *>(api_call_back_context);
  log->status() << api_message_get_string(message) << messaget::eom;
}

int goto_bmc_parse_optionst::doit()
{
  auto api_options = api_optionst::create();

  if(cmdline.isset("version"))
  {
    log.status() << CBMC_VERSION << messaget::eom;
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("help"))
  {
    help();
    return CPROVER_EXIT_SUCCESS;
  }

  api_sessiont api{api_options};

  if(cmdline.args.size() > 1 && !api.is_goto_binary(cmdline.args[0]))
  {
    log.error() << "Please give exactly one binary file" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  std::string filename = cmdline.args[0];

  if(cmdline.isset("validate-goto-model"))
  {
    api_options.validate_goto_model(true);
  }

  log.status() << "goto-bmc version " << *api.get_api_version()
               << messaget::eom;

  // The API works with a callback for querying state - we for now just print
  // collected messages from the message buffer to stdout.
  api.set_message_callback(print_messages_to_stdout, &log);

  // Finally, we read the goto-binary the user supplied...
  api.read_goto_binary(filename);

  // ... and run analysis on it.
  auto result = api.run_verifier();

  return verifier_result_to_exit_code(result->final_result());
}

void goto_bmc_parse_optionst::help()
{
  // clang-format off
  log.status() << '\n' << banner_string("goto-bmc", CBMC_VERSION) << '\n'
               << align_center_with_border("Copyright (C) 2023") << '\n'
               << align_center_with_border("Diffblue Ltd.") << '\n' // NOLINT(*)
               <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    "goto-bmc [-?] [-h] [--help]      show help\n"
    "goto-bmc --version               show version and exit\n"
    // NOLINTNEXTLINE(*)
    "goto-bmc [options] file.c ...    perform bounded model checking on symex-ready goto-binary\n";
  // clang-format on
}
