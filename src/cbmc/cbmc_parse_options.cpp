/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "cbmc_parse_options.h"

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/unicode.h>
#include <util/version.h>

#include <langapi/language.h>

#include <ansi-c/c_preprocess.h>
#include <ansi-c/cprover_library.h>

#include <cpp/cprover_library.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/mm_io.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>

#include <goto-symex/rewrite_union.h>

#include <goto-instrument/reachability_slicer.h>
#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/cover.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include "xml_interface.h"

cbmc_parse_optionst::cbmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(CBMC_OPTIONS, argc, argv),
    xml_interfacet(cmdline),
    messaget(ui_message_handler),
    ui_message_handler(cmdline, std::string("CBMC ") + CBMC_VERSION),
    path_strategy_chooser()
{
}

::cbmc_parse_optionst::cbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options)
  : parse_options_baset(CBMC_OPTIONS + extra_options, argc, argv),
    xml_interfacet(cmdline),
    messaget(ui_message_handler),
    ui_message_handler(cmdline, std::string("CBMC ") + CBMC_VERSION),
    path_strategy_chooser()
{
}

void cbmc_parse_optionst::set_default_options(optionst &options)
{
  // Default true
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("built-in-assertions", true);
  options.set_option("pretty-names", true);
  options.set_option("propagation", true);
  options.set_option("sat-preprocessor", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);

  // Other default
  options.set_option("arrays-uf", "auto");
}

void cbmc_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  cbmc_parse_optionst::set_default_options(options);

  if(cmdline.isset("cover") && cmdline.isset("unwinding-assertions"))
  {
    error() << "--cover and --unwinding-assertions must not be given together"
            << eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("partial-loops") && cmdline.isset("unwinding-assertions"))
  {
    error() << "--partial-loops and --unwinding-assertions must not be given "
            << "together" << eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("reachability-slice") &&
     cmdline.isset("reachability-slice-fb"))
  {
    error() << "--reachability-slice and --reachability-slice-fb must not be "
            << "given together" << eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("full-slice"))
    options.set_option("full-slice", true);

  if(cmdline.isset("show-symex-strategies"))
  {
    std::cout << path_strategy_chooser.show_strategies();
    exit(CPROVER_EXIT_SUCCESS);
  }

  path_strategy_chooser.set_path_strategy_options(cmdline, options, *this);

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);

  if(cmdline.isset("mm"))
    options.set_option("mm", cmdline.get_value("mm"));

  if(cmdline.isset("c89"))
    config.ansi_c.set_c89();

  if(cmdline.isset("c99"))
    config.ansi_c.set_c99();

  if(cmdline.isset("c11"))
    config.ansi_c.set_c11();

  if(cmdline.isset("cpp98"))
    config.cpp.set_cpp98();

  if(cmdline.isset("cpp03"))
    config.cpp.set_cpp03();

  if(cmdline.isset("cpp11"))
    config.cpp.set_cpp11();

  if(cmdline.isset("property"))
    options.set_option("property", cmdline.get_values("property"));

  if(cmdline.isset("drop-unused-functions"))
    options.set_option("drop-unused-functions", true);

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
    cmdline.isset("trace") || cmdline.isset("stack-trace") ||
    cmdline.isset("stop-on-fail"))
    options.set_option("trace", true);

  if(cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);
  if(cmdline.isset("localize-faults-method"))
  {
    options.set_option(
      "localize-faults-method",
      cmdline.get_value("localize-faults-method"));
  }

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("slice-by-trace"))
    options.set_option("slice-by-trace", cmdline.get_value("slice-by-trace"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);

  // transform self loops to assumptions
  options.set_option(
    "self-loops-to-assumptions",
    !cmdline.isset("no-self-loops-to-assumptions"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_values("error-label"));

  // generate unwinding assertions
  if(cmdline.isset("unwinding-assertions"))
    options.set_option("unwinding-assertions", true);

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

  if(cmdline.isset("dimacs"))
    options.set_option("dimacs", true);

  if(cmdline.isset("refine-arrays"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
  }

  if(cmdline.isset("refine-arithmetic"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arithmetic", true);
  }

  if(cmdline.isset("refine"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
    options.set_option("refine-arithmetic", true);
  }

  if(cmdline.isset("refine-strings"))
  {
    options.set_option("refine-strings", true);
    options.set_option("string-printable", cmdline.isset("string-printable"));
  }

  if(cmdline.isset("max-node-refinement"))
    options.set_option(
      "max-node-refinement",
      cmdline.get_value("max-node-refinement"));

  // SMT Options

  if(cmdline.isset("smt1"))
  {
    error() << "--smt1 is no longer supported" << eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("smt2"))
    options.set_option("smt2", true);

  if(cmdline.isset("fpa"))
    options.set_option("fpa", true);

  bool solver_set=false;

  if(cmdline.isset("boolector"))
  {
    options.set_option("boolector", true), solver_set=true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("mathsat"))
  {
    options.set_option("mathsat", true), solver_set=true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("cvc4"))
  {
    options.set_option("cvc4", true), solver_set=true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("yices"))
  {
    options.set_option("yices", true), solver_set=true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("z3"))
  {
    options.set_option("z3", true), solver_set=true;
    options.set_option("smt2", true);
  }

  if(cmdline.isset("smt2") && !solver_set)
  {
    if(cmdline.isset("outfile"))
    {
      // outfile and no solver should give standard compliant SMT-LIB
      options.set_option("generic", true);
    }
    else
    {
      // the default smt2 solver
      options.set_option("z3", true);
    }
  }

  if(cmdline.isset("beautify"))
    options.set_option("beautify", true);

  if(cmdline.isset("no-sat-preprocessor"))
    options.set_option("sat-preprocessor", false);

  if(cmdline.isset("no-pretty-names"))
    options.set_option("pretty-names", false);

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  if(cmdline.isset("graphml-witness"))
  {
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
    options.set_option("stop-on-fail", true);
    options.set_option("trace", true);
  }

  if(cmdline.isset("symex-coverage-report"))
    options.set_option(
      "symex-coverage-report",
      cmdline.get_value("symex-coverage-report"));

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);
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
  try
  {
    get_command_line_options(options);
  }

  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  //
  // Print a banner
  //
  status() << "CBMC version " << CBMC_VERSION << " " << sizeof(void *) * 8
           << "-bit " << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  //
  // Unwinding of transition systems is done by hw-cbmc.
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))
  {
    error() << "This version of CBMC has no support for "
               " hardware modules. Please use hw-cbmc." << eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  register_languages();

  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(get_message_handler())
             ? CPROVER_EXIT_PREPROCESSOR_TEST_FAILED
             : CPROVER_EXIT_SUCCESS;

  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-parse-tree"))
  {
    if(cmdline.args.size()!=1 ||
       is_goto_binary(cmdline.args[0]))
    {
      error() << "Please give exactly one source file" << eom;
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
      error() << "failed to open input file `"
              << filename << "'" << eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      error() << "failed to figure out type of file `"
              <<  filename << "'" << eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->get_language_options(cmdline);
    language->set_message_handler(get_message_handler());

    status() << "Parsing " << filename << eom;

    if(language->parse(infile, filename))
    {
      error() << "PARSING ERROR" << eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->show_parse(std::cout);
    return CPROVER_EXIT_SUCCESS;
  }

  int get_goto_program_ret =
    get_goto_program(goto_model, options, cmdline, *this, ui_message_handler);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  if(cmdline.isset("show-claims") || // will go away
     cmdline.isset("show-properties")) // use this one
  {
    show_properties(
      goto_model, get_message_handler(), ui_message_handler.get_ui());
    return CPROVER_EXIT_SUCCESS;
  }

  if(set_properties())
    return CPROVER_EXIT_SET_PROPERTIES_FAILED;

  return bmct::do_language_agnostic_bmc(
    path_strategy_chooser, options, goto_model, ui_message_handler);
}

bool cbmc_parse_optionst::set_properties()
{
  try
  {
    if(cmdline.isset("claim")) // will go away
      ::set_properties(goto_model, cmdline.get_values("claim"));

    if(cmdline.isset("property")) // use this one
      ::set_properties(goto_model, cmdline.get_values("property"));
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return true;
  }

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
    return true;
  }

  return false;
}

int cbmc_parse_optionst::get_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  const cmdlinet &cmdline,
  messaget &log,
  ui_message_handlert &ui_message_handler)
{
  if(cmdline.args.empty())
  {
    log.error() << "Please provide a program to verify" << log.eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  try
  {
    goto_model = initialize_goto_model(cmdline, ui_message_handler);

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cbmc_parse_optionst::process_goto_program(goto_model, options, log))
      return CPROVER_EXIT_INTERNAL_ERROR;

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
        goto_model,
        ui_message_handler,
        ui_message_handler.get_ui(),
        cmdline.isset("list-goto-functions"));
      return CPROVER_EXIT_SUCCESS;
    }

    log.status() << config.object_bits_info() << log.eom;
  }

  catch(incorrect_goto_program_exceptiont &e)
  {
    log.error() << e.what() << log.eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const char *e)
  {
    log.error() << e << log.eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &e)
  {
    log.error() << e << log.eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(int e)
  {
    log.error() << "Numeric exception : " << e << log.eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::bad_alloc &)
  {
    log.error() << "Out of memory" << log.eom;
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }

  return -1; // no error, continue
}

void cbmc_parse_optionst::preprocessing()
{
  try
  {
    if(cmdline.args.size()!=1)
    {
      error() << "Please provide one program to preprocess" << eom;
      return;
    }

    std::string filename=cmdline.args[0];

    std::ifstream infile(filename);

    if(!infile)
    {
      error() << "failed to open input file" << eom;
      return;
    }

    std::unique_ptr<languaget> language=get_language_from_filename(filename);
    language->get_language_options(cmdline);

    if(language==nullptr)
    {
      error() << "failed to figure out type of file" << eom;
      return;
    }

    language->set_message_handler(get_message_handler());

    if(language->preprocess(infile, filename, std::cout))
      error() << "PREPROCESSING ERROR" << eom;
  }

  catch(const char *e)
  {
    error() << e << eom;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
  }

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
  }
}

bool cbmc_parse_optionst::process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log)
{
  try
  {
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(goto_model);

    // add the library
    log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
                 << eom;
    link_to_library(
      goto_model, log.get_message_handler(), cprover_cpp_library_factory);
    link_to_library(
      goto_model, log.get_message_handler(), cprover_c_library_factory);

    if(options.get_bool_option("string-abstraction"))
      string_instrumentation(goto_model, log.get_message_handler());

    // remove function pointers
    log.status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(
      log.get_message_handler(),
      goto_model,
      options.get_bool_option("pointer-check"));

    mm_io(goto_model);

    // instrument library preconditions
    instrument_preconditions(goto_model);

    // remove returns, gcc vectors, complex
    remove_returns(goto_model);
    remove_vector(goto_model);
    remove_complex(goto_model);
    rewrite_union(goto_model);

    // add generic checks
    log.status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_model);

    // ignore default/user-specified initialization
    // of variables with static lifetime
    if(options.get_bool_option("nondet-static"))
    {
      log.status() << "Adding nondeterministic initialization "
                      "of static/global variables"
                   << eom;
      nondet_static(goto_model);
    }

    if(options.get_bool_option("string-abstraction"))
    {
      log.status() << "String Abstraction" << eom;
      string_abstraction(goto_model, log.get_message_handler());
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(goto_model.symbol_table);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();

    if(options.get_bool_option("drop-unused-functions"))
    {
      // Entry point will have been set before and function pointers removed
      log.status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_model, log.get_message_handler());
    }

    // remove skips such that trivial GOTOs are deleted and not considered
    // for coverage annotation:
    remove_skip(goto_model);

    // instrument cover goals
    if(options.is_set("cover"))
    {
      if(instrument_cover_goals(options, goto_model, log.get_message_handler()))
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
                   << eom;
      if(options.is_set("property"))
        reachability_slicer(
          goto_model, options.get_list_option("property"), true);
      else
        reachability_slicer(goto_model, true);
    }

    if(options.get_bool_option("reachability-slice"))
    {
      log.status() << "Performing a reachability slice" << eom;
      if(options.is_set("property"))
        reachability_slicer(goto_model, options.get_list_option("property"));
      else
        reachability_slicer(goto_model);
    }

    // full slice?
    if(options.get_bool_option("full-slice"))
    {
      log.status() << "Performing a full slice" << eom;
      if(options.is_set("property"))
        property_slicer(goto_model, options.get_list_option("property"));
      else
        full_slicer(goto_model);
    }

    // remove any skips introduced since coverage instrumentation
    remove_skip(goto_model);
  }

  catch(const char *e)
  {
    log.error() << e << eom;
    return true;
  }

  catch(const std::string &e)
  {
    log.error() << e << eom;
    return true;
  }

  catch(int e)
  {
    log.error() << "Numeric exception : " << e << eom;
    return true;
  }

  catch(const std::bad_alloc &)
  {
    log.error() << "Out of memory" << eom;
    exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
    return true;
  }

  return false;
}

/// display command line help
void cbmc_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("CBMC", CBMC_VERSION) << '\n'
            <<
    "* *                 Copyright (C) 2001-2018                 * *\n"
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "* *        Protected in part by U.S. patent 7,225,417       * *\n"
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
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    "\n"
    "C/C++ frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --mm model                   set memory model (default: sc)\n"
    " --arch                       set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    " --c89/99/11                  set C language standard (default: "
                                   << (configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C89?"c89":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C99?"c99":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C11?"c11":"") << ")\n" // NOLINT(*)
    " --cpp98/03/11                set C++ language standard (default: "
                                   << (configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP98?"cpp98": // NOLINT(*)
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP03?"cpp03": // NOLINT(*)
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP11?"cpp11":"") << ")\n" // NOLINT(*)
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    " --round-to-nearest           rounding towards nearest even (default)\n"
    " --round-to-plus-inf          rounding towards plus infinity\n"
    " --round-to-minus-inf         rounding towards minus infinity\n"
    " --round-to-zero              rounding towards zero\n"
    HELP_FUNCTIONS
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --cover CC                   create test-suite with coverage criterion CC\n" // NOLINT(*)
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    HELP_REACHABILITY_SLICER
    " --full-slice                 run full slicer (experimental)\n" // NOLINT(*)
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    "\n"
    "Semantic transformations:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    "\n"
    "BMC options:\n"
    HELP_BMC
    "\n"
    "Backend options:\n"
    " --object-bits n              number of bits used for object addresses\n"
    " --dimacs                     generate CNF in DIMACS format\n"
    " --beautify                   beautify the counterexample (greedy heuristic)\n" // NOLINT(*)
    " --localize-faults            localize faults (experimental)\n"
    " --smt2                       use default SMT2 solver (Z3)\n"
    " --boolector                  use Boolector\n"
    " --mathsat                    use MathSAT\n"
    " --cvc4                       use CVC4\n"
    " --yices                      use Yices\n"
    " --z3                         use Z3\n"
    " --refine                     use refinement procedure (experimental)\n"
    HELP_STRING_REFINEMENT_CBMC
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              bi-directional XML interface\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_GOTO_TRACE
    HELP_FLUSH
    " --verbosity #                verbosity level\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
