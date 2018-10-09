/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#include "jbmc_parse_options.h"

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/unicode.h>
#include <util/xml.h>
#include <util/version.h>

#include <langapi/language.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/lazy_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_properties.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/reachability_slicer.h>
#include <goto-instrument/nondet_static.h>

#include <linking/static_lifetime_init.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include <java_bytecode/convert_java_nondet.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_enum_static_init_unwind_handler.h>
#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>
#include <java_bytecode/remove_java_new.h>
#include <java_bytecode/replace_java_nondet.h>
#include <java_bytecode/simple_method_stubbing.h>

jbmc_parse_optionst::jbmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(JBMC_OPTIONS, argc, argv),
    messaget(ui_message_handler),
    ui_message_handler(cmdline, std::string("JBMC ") + CBMC_VERSION),
    path_strategy_chooser()
{
}

::jbmc_parse_optionst::jbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options)
  : parse_options_baset(JBMC_OPTIONS + extra_options, argc, argv),
    messaget(ui_message_handler),
    ui_message_handler(cmdline, std::string("JBMC ") + CBMC_VERSION),
    path_strategy_chooser()
{
}

void jbmc_parse_optionst::set_default_options(optionst &options)
{
  // Default true
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("built-in-assertions", true);
  options.set_option("lazy-methods", true);
  options.set_option("pretty-names", true);
  options.set_option("propagation", true);
  options.set_option("refine-strings", true);
  options.set_option("sat-preprocessor", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);

  // Other default
  options.set_option("arrays-uf", "auto");
}

void jbmc_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  jbmc_parse_optionst::set_default_options(options);
  parse_java_language_options(cmdline, options);
  parse_object_factory_options(cmdline, options);

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

  // unwind loops in java enum static initialization
  if(cmdline.isset("java-unwind-enum-static"))
    options.set_option("java-unwind-enum-static", true);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);

  // generate unwinding assertions
  if(cmdline.isset("unwinding-assertions"))
    options.set_option("unwinding-assertions", true);

  // generate unwinding assumptions otherwise
  options.set_option(
    "partial-loops",
    cmdline.isset("partial-loops"));

  if(options.get_bool_option("partial-loops") &&
     options.get_bool_option("unwinding-assertions"))
  {
    error() << "--partial-loops and --unwinding-assertions "
            << "must not be given together" << eom;
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  // remove unused equations
  options.set_option(
    "slice-formula",
    cmdline.isset("slice-formula"));

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

  if(cmdline.isset("no-refine-strings"))
    options.set_option("refine-strings", false);

  if(cmdline.isset("string-printable"))
    options.set_option("string-printable", true);

  if(cmdline.isset("no-refine-strings") && cmdline.isset("string-printable"))
  {
    warning() << "--string-printable ignored due to --no-refine-strings" << eom;
  }

  if(
    cmdline.isset("no-refine-strings") &&
    cmdline.isset("max-nondet-string-length"))
  {
    warning() << "--max-nondet-string-length ignored due to "
              << "--no-refine-strings" << eom;
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

  options.set_option(
    "pretty-names",
    !cmdline.isset("no-pretty-names"));

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

  if(cmdline.isset("no-lazy-methods"))
    options.set_option("lazy-methods", false);

  if(cmdline.isset("symex-driven-lazy-loading"))
  {
    options.set_option("symex-driven-lazy-loading", true);
    for(const char *opt :
      { "nondet-static",
        "full-slice",
        "reachability-slice",
        "reachability-slice-fb" })
    {
      if(cmdline.isset(opt))
      {
        throw std::string("Option ") + opt +
          " can't be used with --symex-driven-lazy-loading";
      }
    }
  }

  // The 'allow-pointer-unsoundness' option prevents symex from throwing an
  // exception when it encounters pointers that are shared across threads.
  // This is unsound but given that pointers are ubiquitous in java this check
  // must be disabled in order to support the analysis of multithreaded java
  // code.
  if(cmdline.isset("java-threading"))
    options.set_option("allow-pointer-unsoundness", true);
}

/// invoke main modules
int jbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return 0; // should contemplate EX_OK from sysexits.h
  }

  eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

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
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

  //
  // Print a banner
  //
  status() << "JBMC version " << CBMC_VERSION << " " << sizeof(void *) * 8
           << "-bit " << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  // output the options
  switch(ui_message_handler.get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
      conditional_output(debug(), [&options](messaget::mstreamt &mstream) {
        mstream << "\nOptions: \n";
        options.output(mstream);
        mstream << messaget::eom;
      });
      break;
    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_options;
      json_options["options"] = options.to_json();
      debug() << json_options;
      break;
    }
    case ui_message_handlert::uit::XML_UI:
      debug() << options.to_xml();
      break;
  }

  register_language(new_ansi_c_language);
  register_language(new_java_bytecode_language);

  if(cmdline.isset("show-parse-tree"))
  {
    if(cmdline.args.size()!=1)
    {
      error() << "Please give exactly one source file" << eom;
      return 6;
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
      return 6;
    }

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      error() << "failed to figure out type of file `"
              <<  filename << "'" << eom;
      return 6;
    }

    language->set_language_options(options);
    language->set_message_handler(get_message_handler());

    status() << "Parsing " << filename << eom;

    if(language->parse(infile, filename))
    {
      error() << "PARSING ERROR" << eom;
      return 6;
    }

    language->show_parse(std::cout);
    return 0;
  }

  std::function<void(bmct &, const symbol_tablet &)> configure_bmc = nullptr;
  if(options.get_bool_option("java-unwind-enum-static"))
  {
    configure_bmc = [](bmct &bmc, const symbol_tablet &symbol_table) {
      bmc.add_loop_unwind_handler(
        [&symbol_table](
          const goto_symex_statet::call_stackt &context,
          unsigned loop_number,
          unsigned unwind,
          unsigned &max_unwind) {
          return java_enum_static_init_unwind_handler(
            context, loop_number, unwind, max_unwind, symbol_table);
        });
    };
  }

  object_factory_params.set(options);

  stub_objects_are_not_null =
    options.get_bool_option("java-assume-inputs-non-null");

  if(!cmdline.isset("symex-driven-lazy-loading"))
  {
    std::unique_ptr<goto_modelt> goto_model_ptr;
    int get_goto_program_ret=get_goto_program(goto_model_ptr, options);
    if(get_goto_program_ret!=-1)
      return get_goto_program_ret;

    goto_modelt &goto_model = *goto_model_ptr;

    if(cmdline.isset("show-properties"))
    {
      show_properties(
        goto_model, get_message_handler(), ui_message_handler.get_ui());
      return 0; // should contemplate EX_OK from sysexits.h
    }

    if(set_properties(goto_model))
      return 7; // should contemplate EX_USAGE from sysexits.h

    // The `configure_bmc` callback passed will enable enum-unwind-static if
    // applicable.
    return bmct::do_language_agnostic_bmc(
      path_strategy_chooser,
      options,
      goto_model,
      ui_message_handler,
      configure_bmc);
  }
  else
  {
    // Use symex-driven lazy loading:
    lazy_goto_modelt lazy_goto_model=lazy_goto_modelt::from_handler_object(
      *this, options, get_message_handler());
    lazy_goto_model.initialize(cmdline, options);

    // The precise wording of this error matches goto-symex's complaint when no
    // __CPROVER_start exists (if we just go ahead and run it anyway it will
    // trip an invariant when it tries to load it)
    if(!lazy_goto_model.symbol_table.has_symbol(goto_functionst::entry_point()))
    {
      error() << "the program has no entry point";
      return 6;
    }

    // Add failed symbols for any symbol created prior to loading any
    // particular function:
    add_failed_symbols(lazy_goto_model.symbol_table);

    // Provide show-goto-functions and similar dump functions after symex
    // executes. If --paths is active, these dump routines run after every
    // paths iteration. Its return value indicates that if we ran any dump
    // function, then we should skip the actual solver phase.
    auto callback_after_symex = [this, &lazy_goto_model]() {
      return show_loaded_functions(lazy_goto_model);
    };

    // The `configure_bmc` callback passed will enable enum-unwind-static if
    // applicable.
    return bmct::do_language_agnostic_bmc(
      path_strategy_chooser,
      options,
      lazy_goto_model,
      ui_message_handler,
      configure_bmc,
      callback_after_symex);
  }
}

bool jbmc_parse_optionst::set_properties(goto_modelt &goto_model)
{
  try
  {
    if(cmdline.isset("property"))
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

  catch(int)
  {
    return true;
  }

  return false;
}

int jbmc_parse_optionst::get_goto_program(
  std::unique_ptr<goto_modelt> &goto_model,
  const optionst &options)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to verify" << eom;
    return 6;
  }

  try
  {
    lazy_goto_modelt lazy_goto_model=lazy_goto_modelt::from_handler_object(
      *this, options, get_message_handler());
    lazy_goto_model.initialize(cmdline, options);

    // Show the class hierarchy
    if(cmdline.isset("show-class-hierarchy"))
    {
      class_hierarchyt hierarchy;
      hierarchy(lazy_goto_model.symbol_table);
      show_class_hierarchy(hierarchy, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    // Add failed symbols for any symbol created prior to loading any
    // particular function:
    add_failed_symbols(lazy_goto_model.symbol_table);

    status() << "Generating GOTO Program" << messaget::eom;
    lazy_goto_model.load_all_functions();

    // Show the symbol table before process_goto_functions mangles return
    // values, etc
    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table(
        lazy_goto_model.symbol_table, ui_message_handler);
      return 0;
    }

    // Move the model out of the local lazy_goto_model
    // and into the caller's goto_model
    goto_model=lazy_goto_modelt::process_whole_model_and_freeze(
      std::move(lazy_goto_model));
    if(goto_model == nullptr)
      return 6;

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(ui_message_handler.get_ui(), *goto_model);
      return 0;
    }

    // show it?
    if(
      cmdline.isset("show-goto-functions") ||
      cmdline.isset("list-goto-functions"))
    {
      show_goto_functions(
        *goto_model,
        get_message_handler(),
        ui_message_handler.get_ui(),
        cmdline.isset("list-goto-functions"));
      return 0;
    }

    status() << config.object_bits_info() << eom;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 6;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return 6;
  }

  catch(int)
  {
    return 6;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return 6;
  }

  return -1; // no error, continue
}

void jbmc_parse_optionst::process_goto_function(
  goto_model_functiont &function,
  const abstract_goto_modelt &model,
  const optionst &options)
{
  journalling_symbol_tablet &symbol_table = function.get_symbol_table();
  namespacet ns(symbol_table);
  goto_functionst::goto_functiont &goto_function = function.get_goto_function();

  bool using_symex_driven_loading =
    options.get_bool_option("symex-driven-lazy-loading");

  try
  {
    // Removal of RTTI inspection:
    remove_instanceof(goto_function, symbol_table, get_message_handler());
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(function);

    if(using_symex_driven_loading)
    {
      // remove exceptions
      // If using symex-driven function loading we need to do this now so that
      // symex doesn't have to cope with exception-handling constructs; however
      // the results are slightly worse than running it in whole-program mode
      // (e.g. dead catch sites will be retained)
      remove_exceptions(
        goto_function.body,
        symbol_table,
        get_message_handler(),
        remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF);
    }

    auto function_is_stub = [&symbol_table, &model](const irep_idt &id) {
      return symbol_table.lookup_ref(id).value.is_nil() &&
             !model.can_produce_function(id);
    };

    remove_returns(function, function_is_stub);

    replace_java_nondet(function);

    // Similar removal of java nondet statements:
    convert_nondet(
      function,
      get_message_handler(),
      object_factory_params,
      ID_java);

    // add generic checks
    goto_check(ns, options, ID_java, function.get_goto_function());

    // Replace Java new side effects
    remove_java_new(goto_function, symbol_table, get_message_handler());

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_function, ns);

    // add failed symbols for anything created relating to this particular
    // function (note this means subseqent passes mustn't create more!):
    journalling_symbol_tablet::changesett new_symbols =
      symbol_table.get_inserted();
    for(const irep_idt &new_symbol_name : new_symbols)
    {
      add_failed_symbol_if_needed(
        symbol_table.lookup_ref(new_symbol_name),
        symbol_table);
    }

    // If using symex-driven function loading we must label the assertions
    // now so symex sees its targets; otherwise we leave this until
    // process_goto_functions, as we haven't run remove_exceptions yet, and that
    // pass alters the CFG.
    if(using_symex_driven_loading)
    {
      // label the assertions
      label_properties(goto_function.body);

      goto_function.body.update();
      function.compute_location_numbers();
      goto_function.body.compute_loop_numbers();
    }

    // update the function member in each instruction
    function.update_instructions_function();
  }

  catch(const char *e)
  {
    error() << e << eom;
    throw;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    throw;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    throw;
  }
}

bool jbmc_parse_optionst::show_loaded_functions(
  const abstract_goto_modelt &goto_model)
{
  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(
      goto_model.get_symbol_table(), ui_message_handler);
    return true;
  }

  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(ui_message_handler.get_ui(), goto_model.get_goto_functions());
    return true;
  }

  if(
    cmdline.isset("show-goto-functions") ||
    cmdline.isset("list-goto-functions"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_goto_functions(
      ns,
      get_message_handler(),
      ui_message_handler.get_ui(),
      goto_model.get_goto_functions(),
      cmdline.isset("list-goto-functions"));
    return true;
  }

  if(cmdline.isset("show-properties"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_properties(
      ns,
      get_message_handler(),
      ui_message_handler.get_ui(),
      goto_model.get_goto_functions());
    return true;
  }

  return false;
}

bool jbmc_parse_optionst::process_goto_functions(
  goto_modelt &goto_model,
  const optionst &options)
{
  try
  {
    status() << "Running GOTO functions transformation passes" << eom;

    bool using_symex_driven_loading =
      options.get_bool_option("symex-driven-lazy-loading");

    // When using symex-driven lazy loading, *all* relevant processing is done
    // during process_goto_function, so we have nothing to do here.
    if(using_symex_driven_loading)
      return false;

    // remove catch and throw
    // (introduces instanceof but request it is removed)
    remove_exceptions(
      goto_model,
      get_message_handler(),
      remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF);

    // instrument library preconditions
    instrument_preconditions(goto_model);

    // ignore default/user-specified initialization
    // of variables with static lifetime
    if(cmdline.isset("nondet-static"))
    {
      status() << "Adding nondeterministic initialization "
                  "of static/global variables" << eom;
      nondet_static(goto_model);
    }

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    if(cmdline.isset("drop-unused-functions"))
    {
      // Entry point will have been set before and function pointers removed
      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_model, get_message_handler());
    }

    // remove skips such that trivial GOTOs are deleted
    remove_skip(goto_model);

    // label the assertions
    // This must be done after adding assertions and
    // before using the argument of the "property" option.
    // Do not re-label after using the property slicer because
    // this would cause the property identifiers to change.
    label_properties(goto_model);

    // reachability slice?
    if(cmdline.isset("reachability-slice-fb"))
    {
      if(cmdline.isset("reachability-slice"))
      {
        error() << "--reachability-slice and --reachability-slice-fb "
                << "must not be given together" << eom;
        return true;
      }

      status() << "Performing a forwards-backwards reachability slice" << eom;
      if(cmdline.isset("property"))
        reachability_slicer(goto_model, cmdline.get_values("property"), true);
      else
        reachability_slicer(goto_model, true);
    }

    if(cmdline.isset("reachability-slice"))
    {
      status() << "Performing a reachability slice" << eom;
      if(cmdline.isset("property"))
        reachability_slicer(goto_model, cmdline.get_values("property"));
      else
        reachability_slicer(goto_model);
    }

    // full slice?
    if(cmdline.isset("full-slice"))
    {
      status() << "Performing a full slice" << eom;
      if(cmdline.isset("property"))
        property_slicer(goto_model, cmdline.get_values("property"));
      else
        full_slicer(goto_model);
    }

    // remove any skips introduced
    remove_skip(goto_model);
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

  catch(int)
  {
    return true;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

bool jbmc_parse_optionst::can_generate_function_body(const irep_idt &name)
{
  static const irep_idt initialize_id = INITIALIZE_FUNCTION;

  return name != goto_functionst::entry_point() && name != initialize_id;
}

bool jbmc_parse_optionst::generate_function_body(
  const irep_idt &function_name,
  symbol_table_baset &symbol_table,
  goto_functiont &function,
  bool body_available)
{
  // Provide a simple stub implementation for any function we don't have a
  // bytecode implementation for:

  if(body_available)
    return false;

  if(!can_generate_function_body(function_name))
    return false;

  if(symbol_table.lookup_ref(function_name).mode == ID_java)
  {
    java_generate_simple_method_stub(
      function_name,
      symbol_table,
      stub_objects_are_not_null,
      object_factory_params,
      get_message_handler());

    goto_convert_functionst converter(symbol_table, get_message_handler());
    converter.convert_function(function_name, function);

    return true;
  }
  else
  {
    return false;
  }
}

/// display command line help
void jbmc_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("JBMC", CBMC_VERSION) << '\n'
            <<
    "* *                 Copyright (C) 2001-2018                 * *\n"
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " jbmc [-?] [-h] [--help]      show help\n"
    " jbmc class                   name of class or JAR file to be checked\n"
    "                              In the case of a JAR file, if a main class can be\n" // NOLINT(*)
    "                              inferred from --main-class, --function, or the JAR\n" // NOLINT(*)
    "                              manifest (checked in this order), the behavior is\n" // NOLINT(*)
    "                              the same as running jbmc on the corresponding\n" // NOLINT(*)
    "                              class file."
    "\n"
    "Analysis options:\n"
    HELP_SHOW_PROPERTIES
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    "\n"
    HELP_FUNCTIONS
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --drop-unused-functions      drop functions trivially unreachable\n"
    "                              from main function\n"
    HELP_SHOW_CLASS_HIERARCHY
    "\n"
    "Program instrumentation options:\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    HELP_REACHABILITY_SLICER
    " --full-slice                 run full slicer (experimental)\n" // NOLINT(*)
    "\n"
    "Java Bytecode frontend options:\n"
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    // This one is handled by jbmc_parse_options not by the Java frontend,
    // hence its presence here:
    " --java-threading             enable java multi-threading support (experimental)\n" // NOLINT(*)
    " --java-unwind-enum-static    unwind loops in static initialization of enums\n" // NOLINT(*)
    // Currently only supported in the JBMC frontend:
    " --symex-driven-lazy-loading  only load functions when first entered by symbolic\n" // NOLINT(*)
    "                              execution. Note that --show-symbol-table,\n"
    "                              --show-goto-functions/properties output\n"
    "                              will be restricted to loaded methods in this case,\n" // NOLINT(*)
    "                              and only output after the symex phase.\n"
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
    " --smt1                       use default SMT1 solver (obsolete)\n"
    " --smt2                       use default SMT2 solver (Z3)\n"
    " --boolector                  use Boolector\n"
    " --mathsat                    use MathSAT\n"
    " --cvc4                       use CVC4\n"
    " --yices                      use Yices\n"
    " --z3                         use Z3\n"
    " --refine                     use refinement procedure (experimental)\n"
    HELP_STRING_REFINEMENT
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_GOTO_TRACE
    HELP_FLUSH
    " --verbosity #                verbosity level\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
