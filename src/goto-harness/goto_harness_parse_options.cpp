/******************************************************************\

Module: goto_harness_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_parse_options.h"

#include <cstddef>
#include <set>
#include <string>
#include <utility>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/version.h>

#include "function_call_harness_generator.h"
#include "goto_harness_generator_factory.h"
#include "memory_snapshot_harness_generator.h"

// The basic idea is that this module is handling the following
// sequence of events:
// 1. Initialise a goto-model by parsing an input (goto) binary
// 2. Initialise the harness generator (with some config) that will handle
//    the mutation of the goto-model. The generator should create a new
//    function that can be called by `cbmc --function`. The generated function
//    should implement the behaviour of the harness (What exactly this means
//    depends on the configuration)
// 3. Write the end result of that process to the output binary

int goto_harness_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    log.status() << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  auto got_harness_config = handle_common_options();
  auto factory = make_factory();

  auto factory_options = collect_generate_factory_options();

  // This just sets up the defaults (and would interpret options such as --32).
  config.set(cmdline);

  // Read goto binary into goto-model
  auto read_goto_binary_result =
    read_goto_binary(got_harness_config.in_file, ui_message_handler);
  if(!read_goto_binary_result.has_value())
  {
    throw deserialization_exceptiont{"failed to read goto program from file '" +
                                     got_harness_config.in_file + "'"};
  }
  auto goto_model = std::move(read_goto_binary_result.value());

  // This has to be called after the defaults are set up (as per the
  // config.set(cmdline) above) otherwise, e.g. the architecture specification
  // will be unknown.
  config.set_from_symbol_table(goto_model.symbol_table);

  if(goto_model.symbol_table.has_symbol(
       got_harness_config.harness_function_name))
  {
    throw invalid_command_line_argument_exceptiont(
      "harness function `" +
        id2string(got_harness_config.harness_function_name) +
        "` already in "
        "the symbol table",
      "--" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT);
  }

  // Initialise harness generator
  auto harness_generator = factory.factory(
    got_harness_config.harness_type, factory_options, goto_model);
  CHECK_RETURN(harness_generator != nullptr);

  harness_generator->generate(
    goto_model, got_harness_config.harness_function_name);

  // Write end result to new goto-binary
  if(write_goto_binary(
       got_harness_config.out_file, goto_model, ui_message_handler))
  {
    throw system_exceptiont{"failed to write goto program from file '" +
                            got_harness_config.out_file + "'"};
  }

  return CPROVER_EXIT_SUCCESS;
}

void goto_harness_parse_optionst::help()
{
  log.status()
    << '\n'
    << banner_string("Goto-Harness", CBMC_VERSION) << '\n'
    << align_center_with_border("Copyright (C) 2019") << '\n'
    << align_center_with_border("Diffblue Ltd.") << '\n'
    << align_center_with_border("info@diffblue.com") << '\n'
    << '\n'
    << "Usage:                       Purpose:\n"
    << '\n'
    << " goto-harness [-?] [-h] [--help]  show help\n"
    << " goto-harness --version           show version\n"
    << " goto-harness <in> <out> --harness-function-name <name> --harness-type "
       "<harness-type> [harness options]\n"
    << "\n"
    << "<in> <out>                 goto binaries to read from / write to\n"
    << "--harness-function-name    the name of the harness function to "
       "generate\n"
    << "--harness-type             one of the harness types listed below\n"
    << "\n\n"
    << FUNCTION_HARNESS_GENERATOR_HELP << "\n\n"
    << MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP << messaget::eom;
}

goto_harness_parse_optionst::goto_harness_parse_optionst(
  int argc,
  const char *argv[])
  : parse_options_baset{GOTO_HARNESS_OPTIONS,
                        argc,
                        argv,
                        std::string("GOTO-HARNESS ") + CBMC_VERSION}
{
}

goto_harness_parse_optionst::goto_harness_configt
goto_harness_parse_optionst::handle_common_options()
{
  goto_harness_configt goto_harness_config{};

  // This just checks the positional arguments to be 2.
  // Options are not in .args
  if(cmdline.args.size() != 2)
  {
    help();
    throw invalid_command_line_argument_exceptiont{
      "need to specify both input and output goto binary file names (may be "
      "the same)",
      "<in goto binary> <out goto binary>"};
  }

  goto_harness_config.in_file = cmdline.args[0];
  goto_harness_config.out_file = cmdline.args[1];

  if(!cmdline.isset(GOTO_HARNESS_GENERATOR_TYPE_OPT))
  {
    throw invalid_command_line_argument_exceptiont{
      "required option not set", "--" GOTO_HARNESS_GENERATOR_TYPE_OPT};
  }
  goto_harness_config.harness_type =
    cmdline.get_value(GOTO_HARNESS_GENERATOR_TYPE_OPT);

  // Read the name of the harness function to generate
  if(!cmdline.isset(GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT))
  {
    throw invalid_command_line_argument_exceptiont{
      "required option not set",
      "--" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT};
  }
  goto_harness_config.harness_function_name = {
    cmdline.get_value(GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT)};

  return goto_harness_config;
}

goto_harness_generator_factoryt goto_harness_parse_optionst::make_factory()
{
  auto factory = goto_harness_generator_factoryt{};
  factory.register_generator("call-function", [this]() {
    return util_make_unique<function_call_harness_generatort>(
      ui_message_handler);
  });

  factory.register_generator("initialise-with-memory-snapshot", [this]() {
    return util_make_unique<memory_snapshot_harness_generatort>(
      ui_message_handler);
  });

  return factory;
}

goto_harness_generator_factoryt::generator_optionst
goto_harness_parse_optionst::collect_generate_factory_options()
{
  auto const common_options =
    std::set<std::string>{"version",
                          GOTO_HARNESS_GENERATOR_TYPE_OPT,
                          GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT};

  auto factory_options = goto_harness_generator_factoryt::generator_optionst{};

  for(auto const &option : cmdline.option_names())
  {
    if(common_options.find(option) == common_options.end())
    {
      factory_options.insert({option, cmdline.get_values(option.c_str())});
    }
  }

  return factory_options;
}
