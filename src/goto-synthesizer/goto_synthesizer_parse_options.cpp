/*******************************************************************\
Module: Parse Options Module
Author: Qinheping Hu
\*******************************************************************/

/// \file
/// Main Module

#include "goto_synthesizer_parse_options.h"

#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/write_goto_binary.h>

#include <ansi-c/gcc_version.h>
#include <cbmc/cbmc_parse_options.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/nondet_volatile.h>
#include <goto-instrument/reachability_slicer.h>

#include "enumerative_loop_contracts_synthesizer.h"

#include <fstream>
#include <iostream>

goto_synthesizer_parse_optionst::goto_synthesizer_parse_optionst(
  int argc,
  const char **argv)
  : parse_options_baset(
      GOTO_SYNTHESIZER_OPTIONS CBMC_OPTIONS,
      argc,
      argv,
      "goto-synthesizer")
{
}

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
    cmdline.get_value("verbosity"), messaget::M_STATUS, ui_message_handler);

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

  update_max_malloc_size(goto_model, ui_message_handler);

  // Get options for the backend verifier and preprocess `goto_model`.
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
      std::ofstream out(widen_if_needed(cmdline.args[1]));

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
  code_contractst contracts(
    goto_model,
    log,
    loop_contract_configt{
      true, !cmdline.isset(FLAG_LOOP_CONTRACTS_NO_UNWIND), true});

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
  options.set_option("depth", UINT32_MAX);
  options.set_option("exploration-strategy", "lifo");
  options.set_option("symex-cache-dereferences", false);
  options.set_option("rewrite-rw-ok", true);
  options.set_option("rewrite-union", true);
  options.set_option("self-loops-to-assumptions", true);

  options.set_option("arrays-uf", "auto");
  if(cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if(cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");

  // Generating trace for counterexamples.
  options.set_option("trace", true);

  parse_solver_options(cmdline, options);

  return options;
}

/// display command line help
void goto_synthesizer_parse_optionst::help()
{
  std::cout << '\n'
            << banner_string("Goto-synthesizer", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2022") << '\n'
            << align_center_with_border("Qinheping Hu") << '\n'
            << align_center_with_border("qinhh@amazon.com") << '\n';

  std::cout << help_formatter(
    "\n"
    "Usage:                     \tPurpose:\n"
    "\n"
    " {bgoto-synthesizer} [{y-?}] [{y-h}] [{y--help}] \t show this help\n"
    " {bgoto-synthesizer} {y--version} \t show version and exit\n"
    " {bgoto-synthesizer} {uin} {uout} \t synthesize and apply loop"
    " invariants.\n"
    "\n"
    "Main options:\n" HELP_DUMP_LOOP_CONTRACTS HELP_LOOP_CONTRACTS_NO_UNWIND
    "\n"
    "Accepts all of cbmc's options plus the following backend "
    "options:\n" HELP_CONFIG_BACKEND HELP_SOLVER
    "\n"
    " {y--arrays-uf-never} \t never turn arrays into uninterpreted functions\n"
    " {y--arrays-uf-always} \t always turn arrays into uninterpreted"
    " functions\n"
    "\n"
    "Other options:\n"
    " {y--xml-ui} \t use XML-formatted output\n"
    " {y--json-ui} \t use JSON-formatted output\n"
    " {y--verbosity} {u#} \t verbosity level\n"
    "\n");
}
