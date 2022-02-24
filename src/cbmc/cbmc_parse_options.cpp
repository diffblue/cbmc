/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "cbmc_parse_options.h"

#include <cstdlib> // exit()
#include <fstream>
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/version.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <langapi/language.h>

#include <ansi-c/c_preprocess.h>
#include <ansi-c/cprover_library.h>
#include <ansi-c/gcc_version.h>

#include <assembler/remove_asm.h>

#include <cpp/cprover_library.h>

#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/bmc_util.h>
#include <goto-checker/cover_goals_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/multi_path_symex_only_checker.h>
#include <goto-checker/properties.h>
#include <goto-checker/single_loop_incremental_symex_checker.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-checker/single_path_symex_only_checker.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <goto-instrument/cover.h>
#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/reachability_slicer.h>

#include <goto-symex/path_storage.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include "c_test_input_generator.h"

cbmc_parse_optionst::cbmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      CBMC_OPTIONS,
      argc,
      argv,
      std::string("CBMC ") + CBMC_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

::cbmc_parse_optionst::cbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options)
  : parse_options_baset(
      CBMC_OPTIONS + extra_options,
      argc,
      argv,
      std::string("CBMC ") + CBMC_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

void cbmc_parse_optionst::set_default_options(optionst &options)
{
  // Default true
  options.set_option("built-in-assertions", true);
  options.set_option("pretty-names", true);
  options.set_option("propagation", true);
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);
  options.set_option("show-goto-symex-steps", false);
  options.set_option("show-points-to-sets", false);
  options.set_option("show-array-constraints", false);

  // Other default
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
}

void cbmc_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  cbmc_parse_optionst::set_default_options(options);
  parse_c_object_factory_options(cmdline, options);

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

  if(cmdline.isset("cover") && cmdline.isset("unwinding-assertions"))
  {
    log.error()
      << "--cover and --unwinding-assertions must not be given together"
      << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("max-field-sensitivity-array-size"))
  {
    options.set_option(
      "max-field-sensitivity-array-size",
      cmdline.get_value("max-field-sensitivity-array-size"));
  }

  if(cmdline.isset("no-array-field-sensitivity"))
  {
    if(cmdline.isset("max-field-sensitivity-array-size"))
    {
      log.error()
        << "--no-array-field-sensitivity and --max-field-sensitivity-array-size"
        << " must not be given together" << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("no-array-field-sensitivity", true);
  }

  if(cmdline.isset("partial-loops") && cmdline.isset("unwinding-assertions"))
  {
    log.error()
      << "--partial-loops and --unwinding-assertions must not be given "
      << "together" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("reachability-slice") &&
     cmdline.isset("reachability-slice-fb"))
  {
    log.error()
      << "--reachability-slice and --reachability-slice-fb must not be "
      << "given together" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("full-slice"))
    options.set_option("full-slice", true);

  if(cmdline.isset("show-symex-strategies"))
  {
    log.status() << show_path_strategies() << messaget::eom;
    exit(CPROVER_EXIT_SUCCESS);
  }

  parse_path_strategy_options(cmdline, options, ui_message_handler);

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-byte-ops"))
    options.set_option("show-byte-ops", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);

  if(cmdline.isset("mm"))
    options.set_option("mm", cmdline.get_value("mm"));

  if(cmdline.isset("symex-complexity-limit"))
    options.set_option(
      "symex-complexity-limit", cmdline.get_value("symex-complexity-limit"));

  if(cmdline.isset("symex-complexity-failed-child-loops-limit"))
    options.set_option(
      "symex-complexity-failed-child-loops-limit",
      cmdline.get_value("symex-complexity-failed-child-loops-limit"));

  if(cmdline.isset("property"))
    options.set_option("property", cmdline.get_values("property"));

  if(cmdline.isset("drop-unused-functions"))
    options.set_option("drop-unused-functions", true);

  if(cmdline.isset("havoc-undefined-functions"))
    options.set_option("havoc-undefined-functions", true);

  if(cmdline.isset("string-abstraction"))
    options.set_option("string-abstraction", true);

  if(cmdline.isset("reachability-slice-fb"))
    options.set_option("reachability-slice-fb", true);

  if(cmdline.isset("reachability-slice"))
    options.set_option("reachability-slice", true);

  if(cmdline.isset("nondet-static"))
    options.set_option("nondet-static", true);

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);

  if(cmdline.isset("stop-on-fail") ||
     cmdline.isset("dimacs") ||
     cmdline.isset("outfile"))
    options.set_option("stop-on-fail", true);

  if(
    cmdline.isset("trace") || cmdline.isset("compact-trace") ||
    cmdline.isset("stack-trace") || cmdline.isset("stop-on-fail") ||
    (ui_message_handler.get_ui() != ui_message_handlert::uit::PLAIN &&
     !cmdline.isset("cover")))
  {
    options.set_option("trace", true);
  }

  if(cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("slice-by-trace"))
  {
    log.error() << "--slice-by-trace has been removed" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_values("unwindset"));

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);

  // transform self loops to assumptions
  options.set_option(
    "self-loops-to-assumptions",
    !cmdline.isset("no-self-loops-to-assumptions"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // generate unwinding assertions
  if(cmdline.isset("unwinding-assertions"))
  {
    options.set_option("unwinding-assertions", true);
    options.set_option("paths-symex-explore-all", true);
  }

  if(cmdline.isset("partial-loops"))
    options.set_option("partial-loops", true);

  // remove unused equations
  if(cmdline.isset("slice-formula"))
    options.set_option("slice-formula", true);

  // simplify if conditions and branches
  if(cmdline.isset("no-simplify-if"))
    options.set_option("simplify-if", false);

  if(cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if(cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");

  if(cmdline.isset("show-array-constraints"))
    options.set_option("show-array-constraints", true);

  if(cmdline.isset("refine-strings"))
  {
    options.set_option("refine-strings", true);
    options.set_option("string-printable", cmdline.isset("string-printable"));
  }

  options.set_option(
    "symex-cache-dereferences", cmdline.isset("symex-cache-dereferences"));

  if(cmdline.isset("incremental-loop"))
  {
    options.set_option(
      "incremental-loop", cmdline.get_value("incremental-loop"));
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);

    if(cmdline.isset("unwind-min"))
      options.set_option("unwind-min", cmdline.get_value("unwind-min"));

    if(cmdline.isset("unwind-max"))
      options.set_option("unwind-max", cmdline.get_value("unwind-max"));

    if(cmdline.isset("ignore-properties-before-unwind-min"))
      options.set_option("ignore-properties-before-unwind-min", true);

    if(cmdline.isset("paths"))
    {
      log.error() << "--paths not supported with --incremental-loop"
                  << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
  }

  if(cmdline.isset("no-pretty-names"))
    options.set_option("pretty-names", false);

  if(cmdline.isset("graphml-witness"))
  {
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
    options.set_option("stop-on-fail", true);
    options.set_option("trace", true);
  }

  if(cmdline.isset("symex-coverage-report"))
  {
    options.set_option(
      "symex-coverage-report",
      cmdline.get_value("symex-coverage-report"));
    options.set_option("paths-symex-explore-all", true);
  }

  if(cmdline.isset("validate-ssa-equation"))
  {
    options.set_option("validate-ssa-equation", true);
  }

  if(cmdline.isset("validate-goto-model"))
  {
    options.set_option("validate-goto-model", true);
  }

  if(cmdline.isset("show-goto-symex-steps"))
    options.set_option("show-goto-symex-steps", true);

  if(cmdline.isset("show-points-to-sets"))
    options.set_option("show-points-to-sets", true);

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);

  // Options for process_goto_program
  options.set_option("rewrite-union", true);

  if(cmdline.isset("smt1"))
  {
    log.error() << "--smt1 is no longer supported" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  parse_solver_options(cmdline, options);
}

/// invoke main modules
int cbmc_parse_optionst::doit()
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

  log_version_and_architecture("CBMC");

  //
  // Unwinding of transition systems is done by hw-cbmc.
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))
  {
    log.error() << "This version of CBMC has no support for "
                   " hardware modules. Please use hw-cbmc."
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(cmdline.isset("show-points-to-sets"))
  {
    if(!cmdline.isset("json-ui") || cmdline.isset("xml-ui"))
    {
      log.error() << "--show-points-to-sets supports only"
                     " json output. Use --json-ui."
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  if(cmdline.isset("show-array-constraints"))
  {
    if(!cmdline.isset("json-ui") || cmdline.isset("xml-ui"))
    {
      log.error() << "--show-array-constraints supports only"
                     " json output. Use --json-ui."
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  register_languages();

  // configure gcc, if required
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    configure_gcc(gcc_version);
  }

  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(ui_message_handler)
             ? CPROVER_EXIT_PREPROCESSOR_TEST_FAILED
             : CPROVER_EXIT_SUCCESS;

  if(cmdline.isset("preprocess"))
  {
    preprocessing(options);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-parse-tree"))
  {
    if(
      cmdline.args.size() != 1 ||
      is_goto_binary(cmdline.args[0], ui_message_handler))
    {
      log.error() << "Please give exactly one source file" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::string filename=cmdline.args[0];

    #ifdef _MSC_VER
    std::ifstream infile(widen(filename));
    #else
    std::ifstream infile(filename);
    #endif

    if(!infile)
    {
      log.error() << "failed to open input file '" << filename << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      log.error() << "failed to figure out type of file '" << filename << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->set_language_options(options);
    language->set_message_handler(ui_message_handler);

    log.status() << "Parsing " << filename << messaget::eom;

    if(language->parse(infile, filename))
    {
      log.error() << "PARSING ERROR" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->show_parse(std::cout);
    return CPROVER_EXIT_SUCCESS;
  }

  int get_goto_program_ret =
    get_goto_program(goto_model, options, cmdline, ui_message_handler);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  if(cmdline.isset("show-claims") || // will go away
     cmdline.isset("show-properties")) // use this one
  {
    show_properties(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(set_properties())
    return CPROVER_EXIT_SET_PROPERTIES_FAILED;

  if(
    options.get_bool_option("program-only") ||
    options.get_bool_option("show-vcc") ||
    options.get_bool_option("show-byte-ops"))
  {
    if(options.get_bool_option("paths"))
    {
      all_properties_verifiert<single_path_symex_only_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }
    else
    {
      all_properties_verifiert<multi_path_symex_only_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    options.get_bool_option("dimacs") || !options.get_option("outfile").empty())
  {
    if(options.get_bool_option("paths"))
    {
      stop_on_fail_verifiert<single_path_symex_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }
    else
    {
      stop_on_fail_verifiert<multi_path_symex_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(options.is_set("cover"))
  {
    cover_goals_verifier_with_trace_storaget<multi_path_symex_checkert>
      verifier(options, ui_message_handler, goto_model);
    (void)verifier();
    verifier.report();

    if(options.get_bool_option("show-test-suite"))
    {
      c_test_input_generatort test_generator(ui_message_handler, options);
      test_generator(verifier.get_traces());
    }

    return CPROVER_EXIT_SUCCESS;
  }

  std::unique_ptr<goto_verifiert> verifier = nullptr;

  if(options.is_set("incremental-loop"))
  {
    if(options.get_bool_option("stop-on-fail"))
    {
      verifier = util_make_unique<
        stop_on_fail_verifiert<single_loop_incremental_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
    else
    {
      verifier = util_make_unique<all_properties_verifier_with_trace_storaget<
        single_loop_incremental_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
  }
  else if(
    options.get_bool_option("stop-on-fail") && options.get_bool_option("paths"))
  {
    verifier =
      util_make_unique<stop_on_fail_verifiert<single_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
  }
  else if(
    options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        util_make_unique<stop_on_fail_verifier_with_fault_localizationt<
          multi_path_symex_checkert>>(options, ui_message_handler, goto_model);
    }
    else
    {
      verifier =
        util_make_unique<stop_on_fail_verifiert<multi_path_symex_checkert>>(
          options, ui_message_handler, goto_model);
    }
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    options.get_bool_option("paths"))
  {
    verifier = util_make_unique<
      all_properties_verifier_with_trace_storaget<single_path_symex_checkert>>(
      options, ui_message_handler, goto_model);
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        util_make_unique<all_properties_verifier_with_fault_localizationt<
          multi_path_symex_checkert>>(options, ui_message_handler, goto_model);
    }
    else
    {
      verifier = util_make_unique<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
  }
  else
  {
    UNREACHABLE;
  }

  const resultt result = (*verifier)();
  verifier->report();

  return result_to_exit_code(result);
}

bool cbmc_parse_optionst::set_properties()
{
  if(cmdline.isset("claim")) // will go away
    ::set_properties(goto_model, cmdline.get_values("claim"));

  if(cmdline.isset("property")) // use this one
    ::set_properties(goto_model, cmdline.get_values("property"));

  return false;
}

int cbmc_parse_optionst::get_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  messaget log{ui_message_handler};
  if(cmdline.args.empty())
  {
    log.error() << "Please provide a program to verify" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  goto_model = initialize_goto_model(cmdline.args, ui_message_handler, options);

  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cbmc_parse_optionst::process_goto_program(goto_model, options, log))
    return CPROVER_EXIT_INTERNAL_ERROR;

  if(cmdline.isset("validate-goto-model"))
  {
    goto_model.validate();
  }

  // show it?
  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(ui_message_handler.get_ui(), goto_model);
    return CPROVER_EXIT_SUCCESS;
  }

  // show it?
  if(
    cmdline.isset("show-goto-functions") ||
    cmdline.isset("list-goto-functions"))
  {
    show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
    return CPROVER_EXIT_SUCCESS;
  }

  log.status() << config.object_bits_info() << messaget::eom;

  return -1; // no error, continue
}

void cbmc_parse_optionst::preprocessing(const optionst &options)
{
  if(cmdline.args.size() != 1)
  {
    log.error() << "Please provide one program to preprocess" << messaget::eom;
    return;
  }

  std::string filename = cmdline.args[0];

  std::ifstream infile(filename);

  if(!infile)
  {
    log.error() << "failed to open input file" << messaget::eom;
    return;
  }

  std::unique_ptr<languaget> language = get_language_from_filename(filename);
  language->set_language_options(options);

  if(language == nullptr)
  {
    log.error() << "failed to figure out type of file" << messaget::eom;
    return;
  }

  language->set_message_handler(ui_message_handler);

  if(language->preprocess(infile, filename, std::cout))
    log.error() << "PREPROCESSING ERROR" << messaget::eom;
}

bool cbmc_parse_optionst::process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log)
{
  // Remove inline assembler; this needs to happen before
  // adding the library.
  remove_asm(goto_model);

  // add the library
  log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(
    goto_model, log.get_message_handler(), cprover_cpp_library_factory);
  link_to_library(
    goto_model, log.get_message_handler(), cprover_c_library_factory);

  // Common removal of types and complex constructs
  if(::process_goto_program(goto_model, options, log))
    return true;

  // ignore default/user-specified initialization
  // of variables with static lifetime
  if(options.get_bool_option("nondet-static"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables"
                 << messaget::eom;
    nondet_static(goto_model);
  }

  // add failed symbols
  // needs to be done before pointer analysis
  add_failed_symbols(goto_model.symbol_table);

  if(options.get_bool_option("drop-unused-functions"))
  {
    // Entry point will have been set before and function pointers removed
    log.status() << "Removing unused functions" << messaget::eom;
    remove_unused_functions(goto_model, log.get_message_handler());
  }

  // remove skips such that trivial GOTOs are deleted and not considered
  // for coverage annotation:
  remove_skip(goto_model);

  // instrument cover goals
  if(options.is_set("cover"))
  {
    const auto cover_config = get_cover_config(
      options, goto_model.symbol_table, log.get_message_handler());
    if(instrument_cover_goals(
         cover_config, goto_model, log.get_message_handler()))
      return true;
  }

  // label the assertions
  // This must be done after adding assertions and
  // before using the argument of the "property" option.
  // Do not re-label after using the property slicer because
  // this would cause the property identifiers to change.
  label_properties(goto_model);

  // reachability slice?
  if(options.get_bool_option("reachability-slice-fb"))
  {
    log.status() << "Performing a forwards-backwards reachability slice"
                 << messaget::eom;
    if(options.is_set("property"))
    {
      reachability_slicer(
        goto_model,
        options.get_list_option("property"),
        true,
        log.get_message_handler());
    }
    else
      reachability_slicer(goto_model, true, log.get_message_handler());
  }

  if(options.get_bool_option("reachability-slice"))
  {
    log.status() << "Performing a reachability slice" << messaget::eom;
    if(options.is_set("property"))
    {
      reachability_slicer(
        goto_model,
        options.get_list_option("property"),
        log.get_message_handler());
    }
    else
      reachability_slicer(goto_model, log.get_message_handler());
  }

  // full slice?
  if(options.get_bool_option("full-slice"))
  {
    log.status() << "Performing a full slice" << messaget::eom;
    if(options.is_set("property"))
      property_slicer(goto_model, options.get_list_option("property"));
    else
      full_slicer(goto_model);
  }

  // remove any skips introduced since coverage instrumentation
  remove_skip(goto_model);

  return false;
}

/// display command line help
void cbmc_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("CBMC", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2001-2018") << '\n'
            << align_center_with_border("Daniel Kroening, Edmund Clarke") << '\n' // NOLINT(*)
            << align_center_with_border("Carnegie Mellon University, Computer Science Department") << '\n' // NOLINT(*)
            << align_center_with_border("kroening@kroening.com") << '\n' // NOLINT(*)
            << align_center_with_border("Protected in part by U.S. patent 7,225,417") << '\n' // NOLINT(*)
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " cbmc [-?] [-h] [--help]      show help\n"
    " cbmc file.c ...              source file names\n"
    "\n"
    "Analysis options:\n"
    HELP_SHOW_PROPERTIES
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    "                              (implies --trace)\n"
    " --localize-faults            localize faults (experimental)\n"
    "\n"
    "C/C++ frontend options:\n"
    " --preprocess                 stop after preprocessing\n"
    HELP_CONFIG_C_CPP
    HELP_ANSI_C_LANGUAGE
    HELP_FUNCTIONS
    "\n"
    "Platform options:\n"
    HELP_CONFIG_PLATFORM
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    HELP_COVER
    " --mm MM                      memory consistency model for concurrent programs (default: sc)\n" // NOLINT(*)
    HELP_CONFIG_LIBRARY
    HELP_REACHABILITY_SLICER
    HELP_REACHABILITY_SLICER_FB
    " --full-slice                 run full slicer (experimental)\n" // NOLINT(*)
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    " --havoc-undefined-functions\n"
    "                              for any function that has no body, assign non-deterministic values to\n" // NOLINT(*)
    "                              any parameters passed as non-const pointers and the return value\n" // NOLINT(*)
    "\n"
    "Semantic transformations:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    "\n"
    "BMC options:\n"
    HELP_BMC
    "\n"
    "Backend options:\n"
    HELP_CONFIG_BACKEND
    HELP_SOLVER
    HELP_STRING_REFINEMENT_CBMC
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    HELP_XML_INTERFACE
    HELP_JSON_INTERFACE
    HELP_VALIDATE
    HELP_GOTO_TRACE
    HELP_FLUSH
    " --verbosity #                verbosity level\n"
    HELP_TIMESTAMP
    " --show-array-constraints     show array theory constraints added\n"
    "                              during post processing.\n"
    "                              Requires --json-ui.\n"
    "\n";
  // clang-format on
}
