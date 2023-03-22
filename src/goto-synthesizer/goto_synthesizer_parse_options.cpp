/*******************************************************************\
Module: Parse Options Module
Author: Qinheping Hu
\*******************************************************************/

/// \file
/// Main Module

#include "goto_synthesizer_parse_options.h"

#include <util/exit_codes.h>
#include <util/version.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/write_goto_binary.h>

#include <ansi-c/gcc_version.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/nondet_volatile.h>

#include "enumerative_loop_contracts_synthesizer.h"

#include <fstream>
#include <iostream>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

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

  // configure gcc, if required -- get_goto_program will have set the config
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    configure_gcc(gcc_version);
  }

  // Get options and preprocess `goto_model`.
  const auto &options = get_options();

  // Synthesize loop invariants and annotate them into `goto_model`
  enumerative_loop_contracts_synthesizert synthesizer(goto_model, options, log);
  const auto &invariant_map = synthesizer.synthesize_all();
  const auto &assigns_map = synthesizer.get_assigns_map();

  if(cmdline.isset("dump-loop-contracts"))
  {
    // Default output destination is stdout.
    // Crangler will print the result to screen when the output destination
    // is "stdout".
    std::string json_output_str = "stdout";
    if(cmdline.isset("json-output"))
    {
      json_output_str = cmdline.get_value("json-output");
    }

    namespacet ns(goto_model.symbol_table);
    // Output file specified
    if(cmdline.args.size() == 2)
    {
#ifdef _MSC_VER
      std::ofstream out(widen(cmdline.args[1]));
#else
      std::ofstream out(cmdline.args[1]);
#endif
      if(!out)
      {
        log.error() << "failed to write to '" << cmdline.args[1] << "'";
        return CPROVER_EXIT_CONVERSION_FAILED;
      }
      dump_loop_contracts(
        goto_model, invariant_map, assigns_map, json_output_str, out);
    }
    // No output file specified. Print synthesized contracts with std::cout
    else
    {
      dump_loop_contracts(
        goto_model, invariant_map, assigns_map, json_output_str, std::cout);
    }

    return CPROVER_EXIT_SUCCESS;
  }
  else if(cmdline.isset("json-output"))
  {
    throw invalid_command_line_argument_exceptiont(
      "Incompatible option detected",
      "--json-output must be used with --dump-loop-contracts");
  }

  // Annotate loop contracts.
  annotate_invariants(invariant_map, goto_model);
  annotate_assigns(assigns_map, goto_model);

  // Apply loop contracts.
  std::set<std::string> to_exclude_from_nondet_static(
    cmdline.get_values("nondet-static-exclude").begin(),
    cmdline.get_values("nondet-static-exclude").end());
  code_contractst contracts(goto_model, log);
  contracts.unwind_transformed_loops =
    !cmdline.isset(FLAG_LOOP_CONTRACTS_NO_UNWIND);
  contracts.apply_loop_contracts(to_exclude_from_nondet_static);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // add loop ids
  goto_model.goto_functions.compute_loop_numbers();

  // label the assertions
  label_properties(goto_model);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // write new binary?
  if(cmdline.args.size() == 2)
  {
    log.status() << "Writing GOTO program to '" << cmdline.args[1] << "'"
                 << messaget::eom;

    if(write_goto_binary(cmdline.args[1], goto_model, ui_message_handler))
      return CPROVER_EXIT_CONVERSION_FAILED;
    else
      return CPROVER_EXIT_SUCCESS;
  }
  else if(cmdline.args.size() < 2)
  {
    throw invalid_command_line_argument_exceptiont(
      "Invalid number of positional arguments passed",
      "[in] [out]",
      "goto-instrument needs one input and one output file, aside from other "
      "flags");
  }

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

optionst goto_synthesizer_parse_optionst::get_options()
{
  optionst options;

  // Default options
  // These options are the same as we run CBMC without any set flag.
  options.set_option("built-in-assertions", true);
  options.set_option("propagation", true);
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("show-goto-symex-steps", false);
  options.set_option("show-points-to-sets", false);
  options.set_option("show-array-constraints", false);
  options.set_option("built-in-assertions", true);
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
  options.set_option("exploration-strategy", "lifo");
  options.set_option("symex-cache-dereferences", false);
  options.set_option("rewrite-union", true);
  options.set_option("self-loops-to-assumptions", true);

  // Generating trace for counterexamples.
  options.set_option("trace", true);

  parse_solver_options(cmdline, options);

  return options;
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
    HELP_DUMP_LOOP_CONTRACTS
    HELP_LOOP_CONTRACTS_NO_UNWIND
    "\n"
    "Backend options:\n"
    HELP_CONFIG_BACKEND
    HELP_SOLVER
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    " --verbosity #                verbosity level\n"
    "\n";
  // clang-format on
}
