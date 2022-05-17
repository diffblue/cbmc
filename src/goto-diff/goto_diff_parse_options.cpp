/*******************************************************************\

Module: GOTO-DIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Command Line Option Processing

#include "goto_diff_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/version.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>

#include <ansi-c/cprover_library.h>
#include <ansi-c/gcc_version.h>
#include <assembler/remove_asm.h>
#include <cpp/cprover_library.h>
#include <goto-instrument/cover.h>

#include "change_impact.h"
#include "syntactic_diff.h"
#include "unified_diff.h"

#include <cstdlib> // exit()
#include <fstream>
#include <iostream>

goto_diff_parse_optionst::goto_diff_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      GOTO_DIFF_OPTIONS,
      argc,
      argv,
      std::string("GOTO-DIFF ") + CBMC_VERSION)
{
}

void goto_diff_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  options.set_option("show-properties", cmdline.isset("show-properties"));

  // Options for process_goto_program
  options.set_option("rewrite-union", true);
}

/// invoke main modules
int goto_diff_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);
  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  log_version_and_architecture("GOTO-DIFF");

  if(cmdline.args.size()!=2)
  {
    log.error() << "Please provide two programs to compare" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  register_languages();

  goto_modelt goto_model1 =
    initialize_goto_model({cmdline.args[0]}, ui_message_handler, options);

  // configure gcc, if required -- initialize_goto_model will have set config
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    configure_gcc(gcc_version);
  }

  if(process_goto_program(options, goto_model1))
    return CPROVER_EXIT_INTERNAL_ERROR;
  goto_modelt goto_model2 =
    initialize_goto_model({cmdline.args[1]}, ui_message_handler, options);
  if(process_goto_program(options, goto_model2))
    return CPROVER_EXIT_INTERNAL_ERROR;

  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(ui_message_handler.get_ui(), goto_model1);
    show_loop_ids(ui_message_handler.get_ui(), goto_model2);
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("show-goto-functions") ||
    cmdline.isset("list-goto-functions"))
  {
    show_goto_functions(
      goto_model1, ui_message_handler, cmdline.isset("list-goto-functions"));
    show_goto_functions(
      goto_model2, ui_message_handler, cmdline.isset("list-goto-functions"));
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("change-impact") ||
     cmdline.isset("forward-impact") ||
     cmdline.isset("backward-impact"))
  {
    impact_modet impact_mode=
      cmdline.isset("forward-impact") ?
      impact_modet::FORWARD :
      (cmdline.isset("backward-impact") ?
         impact_modet::BACKWARD :
         impact_modet::BOTH);
    change_impact(
      goto_model1,
      goto_model2,
      impact_mode,
      cmdline.isset("compact-output"));

    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("unified") ||
     cmdline.isset('u'))
  {
    unified_difft u(goto_model1, goto_model2);
    u();
    u.output(std::cout);

    return CPROVER_EXIT_SUCCESS;
  }

  syntactic_difft sd(goto_model1, goto_model2, options, ui_message_handler);
  sd();
  sd.output_functions();

  return CPROVER_EXIT_SUCCESS;
}

bool goto_diff_parse_optionst::process_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  // Remove inline assembler; this needs to happen before
  // adding the library.
  remove_asm(goto_model);

  // add the library
  log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(goto_model, ui_message_handler, cprover_cpp_library_factory);
  link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);

  // Common removal of types and complex constructs
  if(::process_goto_program(goto_model, options, log))
    return true;

  // instrument cover goals
  if(cmdline.isset("cover"))
  {
    // remove skips such that trivial GOTOs are deleted and not considered
    // for coverage annotation:
    remove_skip(goto_model);

    const auto cover_config =
      get_cover_config(options, goto_model.symbol_table, ui_message_handler);
    if(instrument_cover_goals(cover_config, goto_model, ui_message_handler))
      return true;

    goto_model.goto_functions.update();
  }

  // label the assertions
  // This must be done after adding assertions and
  // before using the argument of the "property" option.
  // Do not re-label after using the property slicer because
  // this would cause the property identifiers to change.
  label_properties(goto_model);

  // remove any skips introduced since coverage instrumentation
  remove_skip(goto_model);

  return false;
}

/// display command line help
void goto_diff_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("GOTO_DIFF", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2016") << '\n'
            << align_center_with_border("Daniel Kroening, Peter Schrammel") << '\n' // NOLINT (*)
            << align_center_with_border("kroening@kroening.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto_diff [-?] [-h] [--help]      show help\n"
    " goto_diff old new                 goto binaries to be compared\n"
    "\n"
    "Diff options:\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_SHOW_PROPERTIES
    " --show-loops                 show the loops in the programs\n"
    " -u | --unified               output unified diff\n"
    " --change-impact | \n"
    "  --forward-impact |\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    "  --backward-impact           output unified diff with forward&backward/forward/backward dependencies\n"
    " --compact-output             output dependencies in compact mode\n"
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    HELP_COVER
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_FLUSH
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
