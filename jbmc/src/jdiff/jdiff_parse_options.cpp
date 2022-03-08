/*******************************************************************\

Module: JDIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// JDIFF Command Line Option Processing

#include "jdiff_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/version.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/mm_io.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>

#include <goto-diff/change_impact.h>
#include <goto-diff/unified_diff.h>
#include <goto-instrument/cover.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>

#include "java_syntactic_diff.h"

#include <cstdlib> // exit()
#include <iostream>

jdiff_parse_optionst::jdiff_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      JDIFF_OPTIONS,
      argc,
      argv,
      std::string("JDIFF ") + CBMC_VERSION)
{
}

void jdiff_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  // TODO: improve this when language front ends have been
  //   disentangled from command line parsing
  // we always require these options
  cmdline.set("no-lazy-methods");
  cmdline.set("no-refine-strings");
  parse_java_language_options(cmdline, options);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);

  options.set_option("show-properties", cmdline.isset("show-properties"));
}

/// invoke main modules
int jdiff_parse_optionst::doit()
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

  log_version_and_architecture("JDIFF");

  if(cmdline.args.size() != 2)
  {
    log.error() << "Please provide two programs to compare" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  register_languages();

  goto_modelt goto_model1 =
    initialize_goto_model({cmdline.args[0]}, ui_message_handler, options);
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

  if(
    cmdline.isset("change-impact") || cmdline.isset("forward-impact") ||
    cmdline.isset("backward-impact"))
  {
    impact_modet impact_mode =
      cmdline.isset("forward-impact")
        ? impact_modet::FORWARD
        : (cmdline.isset("backward-impact") ? impact_modet::BACKWARD
                                            : impact_modet::BOTH);
    change_impact(
      goto_model1, goto_model2, impact_mode, cmdline.isset("compact-output"));

    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("unified") || cmdline.isset('u'))
  {
    unified_difft u(goto_model1, goto_model2);
    u();
    u.output(std::cout);

    return CPROVER_EXIT_SUCCESS;
  }

  java_syntactic_difft sd(
    goto_model1, goto_model2, options, ui_message_handler);
  sd();
  sd.output_functions();

  return CPROVER_EXIT_SUCCESS;
}

bool jdiff_parse_optionst::process_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  // remove function pointers
  log.status() << "Removing function pointers and virtual functions"
               << messaget::eom;
  remove_function_pointers(
    ui_message_handler, goto_model, cmdline.isset("pointer-check"));

  // Java virtual functions -> explicit dispatch tables:
  remove_virtual_functions(goto_model);

  // remove Java throw and catch
  // This introduces instanceof, so order is important:
  remove_exceptions_using_instanceof(goto_model, ui_message_handler);

  // Java instanceof -> clsid comparison:
  class_hierarchyt class_hierarchy(goto_model.symbol_table);
  remove_instanceof(goto_model, class_hierarchy, ui_message_handler);

  mm_io(goto_model);

  // instrument library preconditions
  instrument_preconditions(goto_model);

  // remove returns
  remove_returns(goto_model);

  transform_assertions_assumptions(options, goto_model);

  // checks don't know about adjusted float expressions
  adjust_float_expressions(goto_model);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // instrument cover goals
  if(cmdline.isset("cover"))
  {
    // remove skips such that trivial GOTOs are deleted and not considered for
    // coverage annotation:
    remove_skip(goto_model);

    const auto cover_config =
      get_cover_config(options, goto_model.symbol_table, ui_message_handler);
    if(instrument_cover_goals(cover_config, goto_model, ui_message_handler))
      return true;
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
void jdiff_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("JDIFF", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2016-2018") << '\n'
            << align_center_with_border("Daniel Kroening, Peter Schrammel") << '\n' // NOLINT(*)
            << align_center_with_border("kroening@kroening.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " jdiff [-?] [-h] [--help]      show help\n"
    " jdiff old new                 jars to be compared\n"
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
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    HELP_COVER
    "Java Bytecode frontend options:\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    "Other options:\n"
    " --version                    show version and exit\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
