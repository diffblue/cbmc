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

  if(cmdline.args.size() != 1 || !api.is_goto_binary(cmdline.args[0]))
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
  struct call_back_contextt
  {
    std::reference_wrapper<messaget> log;
    bool error_seen;
  } call_back_context{log};
  const auto callback = [](
                          const api_messaget &message,
                          api_call_back_contextt api_call_back_context) {
    auto context = static_cast<call_back_contextt *>(api_call_back_context);
    const bool is_error_message = api_message_is_error(message);
    context->error_seen |= is_error_message;
    (is_error_message ? context->log.get().error()
                      : context->log.get().status())
      << api_message_get_string(message) << messaget::eom;
  };

  api.set_message_callback(callback, &call_back_context);

  // Finally, we read the goto-binary the user supplied...
  api.read_goto_binary(filename);
  if(call_back_context.error_seen)
    return CPROVER_EXIT_PARSE_ERROR;

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
  log.status() << messaget::eom;
}
