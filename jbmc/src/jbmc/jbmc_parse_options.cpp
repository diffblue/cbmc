/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#include "jbmc_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/version.h>
#include <util/xml.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <ansi-c/ansi_c_language.h>
#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>
#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/reachability_slicer.h>
#include <goto-symex/path_storage.h>
#include <java_bytecode/convert_java_nondet.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_multi_path_symex_checker.h>
#include <java_bytecode/java_multi_path_symex_only_checker.h>
#include <java_bytecode/java_single_path_symex_checker.h>
#include <java_bytecode/java_single_path_symex_only_checker.h>
#include <java_bytecode/lazy_goto_model.h>
#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>
#include <java_bytecode/remove_java_new.h>
#include <java_bytecode/replace_java_nondet.h>
#include <java_bytecode/simple_method_stubbing.h>
#include <langapi/language.h>
#include <langapi/mode.h>
#include <linking/static_lifetime_init.h>
#include <pointer-analysis/add_failed_symbols.h>

#include <cstdlib> // exit()
#include <iostream>
#include <memory>

jbmc_parse_optionst::jbmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      JBMC_OPTIONS,
      argc,
      argv,
      std::string("JBMC ") + CBMC_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

::jbmc_parse_optionst::jbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options)
  : parse_options_baset(
      JBMC_OPTIONS + extra_options,
      argc,
      argv,
      std::string("JBMC ") + CBMC_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
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
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);
  options.set_option("show-goto-symex-steps", false);

  // Other default
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
}

void jbmc_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  jbmc_parse_optionst::set_default_options(options);

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

  parse_java_language_options(cmdline, options);
  parse_java_object_factory_options(cmdline, options);

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

  if(cmdline.isset("show-symex-strategies"))
  {
    log.status() << show_path_strategies() << messaget::eom;
    exit(CPROVER_EXIT_SUCCESS);
  }

  parse_path_strategy_options(cmdline, options, ui_message_handler);

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
    cmdline.isset("trace") || cmdline.isset("compact-trace") ||
    cmdline.isset("stack-trace") || cmdline.isset("stop-on-fail") ||
    (ui_message_handler.get_ui() != ui_message_handlert::uit::PLAIN &&
     !cmdline.isset("cover")))
  {
    options.set_option("trace", true);
  }

  if(cmdline.isset("validate-trace"))
  {
    options.set_option("validate-trace", true);
    options.set_option("trace", true);
  }

  if(cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);

  if(cmdline.isset("symex-complexity-limit"))
  {
    options.set_option(
      "symex-complexity-limit", cmdline.get_value("symex-complexity-limit"));
  }

  if(cmdline.isset("symex-complexity-failed-child-loops-limit"))
  {
    options.set_option(
      "symex-complexity-failed-child-loops-limit",
      cmdline.get_value("symex-complexity-failed-child-loops-limit"));
  }

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);

  // transform self loops to assumptions
  options.set_option(
    "self-loops-to-assumptions",
    !cmdline.isset("no-self-loops-to-assumptions"));

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

  if(cmdline.isset("no-refine-strings"))
    options.set_option("refine-strings", false);

  if(cmdline.isset("string-printable") && cmdline.isset("no-refine-strings"))
  {
    throw invalid_command_line_argument_exceptiont(
      "cannot use --string-printable with --no-refine-strings",
      "--string-printable");
  }

  if(cmdline.isset("string-input-value") && cmdline.isset("no-refine-strings"))
  {
    throw invalid_command_line_argument_exceptiont(
      "cannot use --string-input-value with --no-refine-strings",
      "--string-input-value");
  }

  if(
    cmdline.isset("no-refine-strings") &&
    cmdline.isset("max-nondet-string-length"))
  {
    throw invalid_command_line_argument_exceptiont(
      "cannot use --max-nondet-string-length with --no-refine-strings",
      "--max-nondet-string-length");
  }

  options.set_option(
    "pretty-names",
    !cmdline.isset("no-pretty-names"));

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

  if(cmdline.isset("validate-ssa-equation"))
  {
    options.set_option("validate-ssa-equation", true);
  }

  if(cmdline.isset("validate-goto-model"))
  {
    options.set_option("validate-goto-model", true);
  }

  options.set_option(
    "symex-cache-dereferences", cmdline.isset("symex-cache-dereferences"));

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

  if(cmdline.isset("show-goto-symex-steps"))
    options.set_option("show-goto-symex-steps", true);

  if(cmdline.isset("smt1"))
  {
    log.error() << "--smt1 is no longer supported" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  parse_solver_options(cmdline, options);
}

/// invoke main modules
int jbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  log_version_and_architecture("JBMC");

  // output the options
  switch(ui_message_handler.get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
      log.conditional_output(
        log.debug(), [&options](messaget::mstreamt &debug_stream) {
          debug_stream << "\nOptions: \n";
          options.output(debug_stream);
          debug_stream << messaget::eom;
        });
      break;
    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_options{{"options", options.to_json()}};
      log.debug() << json_options;
      break;
    }
    case ui_message_handlert::uit::XML_UI:
      log.debug() << options.to_xml();
      break;
  }

  register_language(new_ansi_c_language);
  register_language(new_java_bytecode_language);

  if(!((cmdline.isset("jar") && cmdline.args.empty()) ||
       (cmdline.isset("gb") && cmdline.args.empty()) ||
       (!cmdline.isset("jar") && !cmdline.isset("gb") &&
        (cmdline.args.size() == 1))))
  {
    log.error() << "Please give exactly one class name, "
                << "and/or use -jar jarfile or --gb goto-binary"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if((cmdline.args.size() == 1) && !cmdline.isset("show-parse-tree"))
  {
    std::string main_class = cmdline.args[0];
    // `java` accepts slashes and dots as package separators
    std::replace(main_class.begin(), main_class.end(), '/', '.');
    config.java.main_class = main_class;
    cmdline.args.pop_back();
  }

  if(cmdline.isset("jar"))
  {
    cmdline.args.push_back(cmdline.get_value("jar"));
  }

  if(cmdline.isset("gb"))
  {
    cmdline.args.push_back(cmdline.get_value("gb"));
  }

  // Shows the parse tree of the main class
  if(cmdline.isset("show-parse-tree"))
  {
    std::unique_ptr<languaget> language = get_language_from_mode(ID_java);
    CHECK_RETURN(language != nullptr);
    language->set_language_options(options);
    language->set_message_handler(ui_message_handler);

    log.status() << "Parsing ..." << messaget::eom;

    if(static_cast<java_bytecode_languaget *>(language.get())->parse())
    {
      log.error() << "PARSING ERROR" << messaget::eom;
      return CPROVER_EXIT_PARSE_ERROR;
    }

    language->show_parse(std::cout);
    return CPROVER_EXIT_SUCCESS;
  }

  object_factory_params.set(options);

  stub_objects_are_not_null =
    options.get_bool_option("java-assume-inputs-non-null");

  std::unique_ptr<abstract_goto_modelt> goto_model_ptr;
  int get_goto_program_ret = get_goto_program(goto_model_ptr, options);
  if(get_goto_program_ret != -1)
    return get_goto_program_ret;

  if(
    options.get_bool_option("program-only") ||
    options.get_bool_option("show-vcc") ||
    (options.get_bool_option("symex-driven-lazy-loading") &&
     (cmdline.isset("show-symbol-table") || cmdline.isset("list-symbols") ||
      cmdline.isset("show-goto-functions") ||
      cmdline.isset("list-goto-functions") ||
      cmdline.isset("show-properties") || cmdline.isset("show-loops"))))
  {
    if(options.get_bool_option("paths"))
    {
      all_properties_verifiert<java_single_path_symex_only_checkert> verifier(
        options, ui_message_handler, *goto_model_ptr);
      (void)verifier();
    }
    else
    {
      all_properties_verifiert<java_multi_path_symex_only_checkert> verifier(
        options, ui_message_handler, *goto_model_ptr);
      (void)verifier();
    }

    if(options.get_bool_option("symex-driven-lazy-loading"))
    {
      // We can only output these after goto-symex has run.
      (void)show_loaded_symbols(*goto_model_ptr);
      (void)show_loaded_functions(*goto_model_ptr);
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    options.get_bool_option("dimacs") || !options.get_option("outfile").empty())
  {
    if(options.get_bool_option("paths"))
    {
      stop_on_fail_verifiert<java_single_path_symex_checkert> verifier(
        options, ui_message_handler, *goto_model_ptr);
      (void)verifier();
    }
    else
    {
      stop_on_fail_verifiert<java_multi_path_symex_checkert> verifier(
        options, ui_message_handler, *goto_model_ptr);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  std::unique_ptr<goto_verifiert> verifier = nullptr;

  if(
    options.get_bool_option("stop-on-fail") && options.get_bool_option("paths"))
  {
    verifier =
      util_make_unique<stop_on_fail_verifiert<java_single_path_symex_checkert>>(
        options, ui_message_handler, *goto_model_ptr);
  }
  else if(
    options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        util_make_unique<stop_on_fail_verifier_with_fault_localizationt<
          java_multi_path_symex_checkert>>(
          options, ui_message_handler, *goto_model_ptr);
    }
    else
    {
      verifier = util_make_unique<
        stop_on_fail_verifiert<java_multi_path_symex_checkert>>(
        options, ui_message_handler, *goto_model_ptr);
    }
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    options.get_bool_option("paths"))
  {
    verifier = util_make_unique<all_properties_verifier_with_trace_storaget<
      java_single_path_symex_checkert>>(
      options, ui_message_handler, *goto_model_ptr);
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        util_make_unique<all_properties_verifier_with_fault_localizationt<
          java_multi_path_symex_checkert>>(
          options, ui_message_handler, *goto_model_ptr);
    }
    else
    {
      verifier = util_make_unique<all_properties_verifier_with_trace_storaget<
        java_multi_path_symex_checkert>>(
        options, ui_message_handler, *goto_model_ptr);
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

int jbmc_parse_optionst::get_goto_program(
  std::unique_ptr<abstract_goto_modelt> &goto_model_ptr,
  const optionst &options)
{
  if(options.is_set("context-include") || options.is_set("context-exclude"))
    method_context = get_context(options);
  lazy_goto_modelt lazy_goto_model =
    lazy_goto_modelt::from_handler_object(*this, options, ui_message_handler);
  lazy_goto_model.initialize(cmdline.args, options);

  class_hierarchy =
    util_make_unique<class_hierarchyt>(lazy_goto_model.symbol_table);

  // Show the class hierarchy
  if(cmdline.isset("show-class-hierarchy"))
  {
    show_class_hierarchy(*class_hierarchy, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  // Add failed symbols for any symbol created prior to loading any
  // particular function:
  add_failed_symbols(lazy_goto_model.symbol_table);

  if(!options.get_bool_option("symex-driven-lazy-loading"))
  {
    log.status() << "Generating GOTO Program" << messaget::eom;
    lazy_goto_model.load_all_functions();

    // show symbol table or list symbols
    if(show_loaded_symbols(lazy_goto_model))
      return CPROVER_EXIT_SUCCESS;

    // Move the model out of the local lazy_goto_model
    // and into the caller's goto_model
    goto_model_ptr = lazy_goto_modelt::process_whole_model_and_freeze(
      std::move(lazy_goto_model));
    if(goto_model_ptr == nullptr)
      return CPROVER_EXIT_INTERNAL_ERROR;

    goto_modelt &goto_model = dynamic_cast<goto_modelt &>(*goto_model_ptr);

    if(cmdline.isset("validate-goto-model"))
    {
      goto_model.validate();
    }

    if(show_loaded_functions(goto_model))
      return CPROVER_EXIT_SUCCESS;

    if(cmdline.isset("property"))
      ::set_properties(goto_model, cmdline.get_values("property"));
  }
  else
  {
    // The precise wording of this error matches goto-symex's complaint when no
    // __CPROVER_start exists (if we just go ahead and run it anyway it will
    // trip an invariant when it tries to load it)
    if(!lazy_goto_model.symbol_table.has_symbol(goto_functionst::entry_point()))
    {
      log.error() << "the program has no entry point" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    if(cmdline.isset("validate-goto-model"))
    {
      lazy_goto_model.validate();
    }

    goto_model_ptr =
      util_make_unique<lazy_goto_modelt>(std::move(lazy_goto_model));
  }

  log.status() << config.object_bits_info() << messaget::eom;

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

  // Removal of RTTI inspection:
  remove_instanceof(
    function.get_function_id(),
    goto_function,
    symbol_table,
    *class_hierarchy,
    ui_message_handler);
  // Java virtual functions -> explicit dispatch tables:
  remove_virtual_functions(function, *class_hierarchy);

  auto function_is_stub = [&symbol_table, &model](const irep_idt &id) {
    return symbol_table.lookup_ref(id).value.is_nil() &&
           !model.can_produce_function(id);
  };

  remove_returns(function, function_is_stub);

  replace_java_nondet(function);

  // Similar removal of java nondet statements:
  convert_nondet(function, ui_message_handler, object_factory_params, ID_java);

  if(using_symex_driven_loading)
  {
    // remove exceptions
    // If using symex-driven function loading we need to do this now so that
    // symex doesn't have to cope with exception-handling constructs; however
    // the results are slightly worse than running it in whole-program mode
    // (e.g. dead catch sites will be retained)
    remove_exceptions(
      function.get_function_id(),
      goto_function.body,
      symbol_table,
      *class_hierarchy.get(),
      ui_message_handler);
  }

  transform_assertions_assumptions(options, function.get_goto_function().body);

  // Replace Java new side effects
  remove_java_new(
    function.get_function_id(),
    goto_function,
    symbol_table,
    ui_message_handler);

  // checks don't know about adjusted float expressions
  adjust_float_expressions(goto_function, ns);

  // add failed symbols for anything created relating to this particular
  // function (note this means subsequent passes mustn't create more!):
  journalling_symbol_tablet::changesett new_symbols =
    symbol_table.get_inserted();
  for(const irep_idt &new_symbol_name : new_symbols)
  {
    add_failed_symbol_if_needed(
      symbol_table.lookup_ref(new_symbol_name), symbol_table);
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
}

bool jbmc_parse_optionst::show_loaded_symbols(
  const abstract_goto_modelt &goto_model)
{
  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(goto_model.get_symbol_table(), ui_message_handler);
    return true;
  }
  else if(cmdline.isset("list-symbols"))
  {
    show_symbol_table_brief(goto_model.get_symbol_table(), ui_message_handler);
    return true;
  }

  return false;
}

bool jbmc_parse_optionst::show_loaded_functions(
  const abstract_goto_modelt &goto_model)
{
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
      ui_message_handler,
      goto_model.get_goto_functions(),
      cmdline.isset("list-goto-functions"));
    return true;
  }

  if(cmdline.isset("show-properties"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_properties(ns, ui_message_handler, goto_model.get_goto_functions());
    return true;
  }

  return false;
}

bool jbmc_parse_optionst::process_goto_functions(
  goto_modelt &goto_model,
  const optionst &options)
{
  log.status() << "Running GOTO functions transformation passes"
               << messaget::eom;

  bool using_symex_driven_loading =
    options.get_bool_option("symex-driven-lazy-loading");

  // When using symex-driven lazy loading, *all* relevant processing is done
  // during process_goto_function, so we have nothing to do here.
  if(using_symex_driven_loading)
    return false;

  // remove catch and throw
  remove_exceptions(goto_model, *class_hierarchy.get(), ui_message_handler);

  // instrument library preconditions
  instrument_preconditions(goto_model);

  // ignore default/user-specified initialization
  // of variables with static lifetime
  if(cmdline.isset("nondet-static"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables"
                 << messaget::eom;
    nondet_static(goto_model);
  }

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  if(cmdline.isset("drop-unused-functions"))
  {
    // Entry point will have been set before and function pointers removed
    log.status() << "Removing unused functions" << messaget::eom;
    remove_unused_functions(goto_model, ui_message_handler);
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
      log.error() << "--reachability-slice and --reachability-slice-fb "
                  << "must not be given together" << messaget::eom;
      return true;
    }

    log.status() << "Performing a forwards-backwards reachability slice"
                 << messaget::eom;
    if(cmdline.isset("property"))
    {
      reachability_slicer(
        goto_model, cmdline.get_values("property"), true, ui_message_handler);
    }
    else
      reachability_slicer(goto_model, true, ui_message_handler);
  }

  if(cmdline.isset("reachability-slice"))
  {
    log.status() << "Performing a reachability slice" << messaget::eom;
    if(cmdline.isset("property"))
    {
      reachability_slicer(
        goto_model, cmdline.get_values("property"), ui_message_handler);
    }
    else
      reachability_slicer(goto_model, ui_message_handler);
  }

  // full slice?
  if(cmdline.isset("full-slice"))
  {
    log.status() << "Performing a full slice" << messaget::eom;
    if(cmdline.isset("property"))
      property_slicer(goto_model, cmdline.get_values("property"));
    else
      full_slicer(goto_model);
  }

  // remove any skips introduced
  remove_skip(goto_model);

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

  if(
    body_available &&
    (!method_context || (*method_context)(id2string(function_name))))
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
      ui_message_handler);

    goto_convert_functionst converter(symbol_table, ui_message_handler);
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
            << align_center_with_border("Copyright (C) 2001-2018") << '\n'
            << align_center_with_border("Daniel Kroening, Edmund Clarke") << '\n' // NOLINT(*)
            << align_center_with_border("Carnegie Mellon University, Computer Science Department") << '\n' // NOLINT(*)
            << align_center_with_border("kroening@kroening.com") << '\n'
            << "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " jbmc [-?] [-h] [--help]      show help\n"
    " jbmc\n"
    HELP_JAVA_METHOD_NAME
    " jbmc\n"
    HELP_JAVA_CLASS_NAME
    " jbmc\n"
    HELP_JAVA_JAR
    " jbmc\n"
    HELP_JAVA_GOTO_BINARY
    "\n"
    HELP_JAVA_CLASSPATH
    HELP_FUNCTIONS
    "\n"
    "Analysis options:\n"
    HELP_SHOW_PROPERTIES
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    "                              (implies --trace)\n"
    HELP_JAVA_TRACE_VALIDATION
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    " --list-symbols               list symbols with type information\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --drop-unused-functions      drop functions trivially unreachable\n"
    "                              from main function\n"
    HELP_SHOW_CLASS_HIERARCHY
    "\n"
    "Program instrumentation options:\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    HELP_REACHABILITY_SLICER
    " --full-slice                 run full slicer (experimental)\n" // NOLINT(*)
    "\n"
    "Java Bytecode frontend options:\n"
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
    HELP_CONFIG_BACKEND
    HELP_SOLVER
    HELP_STRING_REFINEMENT
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
    "\n";
  // clang-format on
}
