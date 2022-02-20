/*******************************************************************\

Module: JANALYZER Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JANALYZER Command Line Option Processing

#include "janalyzer_parse_options.h"

#include <cstdlib> // exit()
#include <fstream>
#include <iostream>
#include <memory>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <analyses/constant_propagator.h>
#include <analyses/dependence_graph.h>
#include <analyses/goto_check.h>
#include <analyses/interval_domain.h>
#include <analyses/local_may_alias.h>

#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/lazy_goto_model.h>
#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include <linking/static_lifetime_init.h>

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/version.h>

#include <goto-analyzer/static_show_domain.h>
#include <goto-analyzer/static_simplifier.h>
#include <goto-analyzer/static_verifier.h>
#include <goto-analyzer/taint_analysis.h>
#include <goto-analyzer/unreachable_instructions.h>

janalyzer_parse_optionst::janalyzer_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      JANALYZER_OPTIONS,
      argc,
      argv,
      std::string("JANALYZER ") + CBMC_VERSION)
{
}

void janalyzer_parse_optionst::register_languages()
{
  // Need ansi C language for __CPROVER_rounding_mode
  register_language(new_ansi_c_language);
  register_language(new_java_bytecode_language);
}

void janalyzer_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

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

  // Select a specific analysis
  if(cmdline.isset("taint"))
  {
    options.set_option("taint", true);
    options.set_option("specific-analysis", true);
  }
  // For backwards compatibility,
  // these are first recognised as specific analyses
  bool reachability_task = false;
  if(cmdline.isset("unreachable-instructions"))
  {
    options.set_option("unreachable-instructions", true);
    options.set_option("specific-analysis", true);
    reachability_task = true;
  }
  if(cmdline.isset("unreachable-functions"))
  {
    options.set_option("unreachable-functions", true);
    options.set_option("specific-analysis", true);
    reachability_task = true;
  }
  if(cmdline.isset("reachable-functions"))
  {
    options.set_option("reachable-functions", true);
    options.set_option("specific-analysis", true);
    reachability_task = true;
  }
  if(cmdline.isset("show-local-may-alias"))
  {
    options.set_option("show-local-may-alias", true);
    options.set_option("specific-analysis", true);
  }

  // Output format choice
  if(cmdline.isset("text"))
  {
    options.set_option("text", true);
    options.set_option("outfile", cmdline.get_value("text"));
  }
  else if(cmdline.isset("json"))
  {
    options.set_option("json", true);
    options.set_option("outfile", cmdline.get_value("json"));
  }
  else if(cmdline.isset("xml"))
  {
    options.set_option("xml", true);
    options.set_option("outfile", cmdline.get_value("xml"));
  }
  else if(cmdline.isset("dot"))
  {
    options.set_option("dot", true);
    options.set_option("outfile", cmdline.get_value("dot"));
  }
  else
  {
    options.set_option("text", true);
    options.set_option("outfile", "-");
  }

  // The use should either select:
  //  1. a specific analysis, or
  //  2. a triple of task / analyzer / domain, or
  //  3. one of the general display options

  // Task options
  if(cmdline.isset("show"))
  {
    options.set_option("show", true);
    options.set_option("general-analysis", true);
  }
  else if(cmdline.isset("verify"))
  {
    options.set_option("verify", true);
    options.set_option("general-analysis", true);
  }
  else if(cmdline.isset("simplify"))
  {
    options.set_option("simplify", true);
    options.set_option("outfile", cmdline.get_value("simplify"));
    options.set_option("general-analysis", true);

    // For development allow slicing to be disabled in the simplify task
    options.set_option(
      "simplify-slicing", !(cmdline.isset("no-simplify-slicing")));
  }
  else if(cmdline.isset("show-intervals"))
  {
    // For backwards compatibility
    options.set_option("show", true);
    options.set_option("general-analysis", true);
    options.set_option("intervals", true);
    options.set_option("domain set", true);
  }
  else if(cmdline.isset("(show-non-null)"))
  {
    // For backwards compatibility
    options.set_option("show", true);
    options.set_option("general-analysis", true);
    options.set_option("non-null", true);
    options.set_option("domain set", true);
  }
  else if(cmdline.isset("intervals") || cmdline.isset("non-null"))
  {
    // For backwards compatibility either of these on their own means show
    options.set_option("show", true);
    options.set_option("general-analysis", true);
  }

  if(options.get_bool_option("general-analysis") || reachability_task)
  {
    // Abstract interpreter choice
    if(cmdline.isset("location-sensitive"))
      options.set_option("location-sensitive", true);
    else if(cmdline.isset("concurrent"))
      options.set_option("concurrent", true);
    else
    {
      // Silently default to location-sensitive as it's the "default"
      // view of abstract interpretation.
      options.set_option("location-sensitive", true);
    }

    // Domain choice
    if(cmdline.isset("constants"))
    {
      options.set_option("constants", true);
      options.set_option("domain set", true);
    }
    else if(cmdline.isset("dependence-graph"))
    {
      options.set_option("dependence-graph", true);
      options.set_option("domain set", true);
    }
    else if(cmdline.isset("intervals"))
    {
      options.set_option("intervals", true);
      options.set_option("domain set", true);
    }
    else if(cmdline.isset("non-null"))
    {
      options.set_option("non-null", true);
      options.set_option("domain set", true);
    }

    // Reachability questions, when given with a domain swap from specific
    // to general tasks so that they can use the domain & parameterisations.
    if(reachability_task)
    {
      if(options.get_bool_option("domain set"))
      {
        options.set_option("specific-analysis", false);
        options.set_option("general-analysis", true);
      }
    }
    else
    {
      if(!options.get_bool_option("domain set"))
      {
        // Default to constants as it is light-weight but useful
        log.status() << "Domain not specified, defaulting to --constants"
                     << messaget::eom;
        options.set_option("constants", true);
      }
    }
  }
}

/// For the task, build the appropriate kind of analyzer
/// Ideally this should be a pure function of options.
/// However at the moment some domains require the goto_model
ai_baset *janalyzer_parse_optionst::build_analyzer(
  goto_modelt &goto_model,
  const optionst &options,
  const namespacet &ns)
{
  ai_baset *domain = nullptr;

  if(options.get_bool_option("location-sensitive"))
  {
    if(options.get_bool_option("constants"))
    {
      // constant_propagator_ait derives from ait<constant_propagator_domaint>
      domain = new constant_propagator_ait(goto_model.goto_functions);
    }
    else if(options.get_bool_option("dependence-graph"))
    {
      domain = new dependence_grapht(ns);
    }
    else if(options.get_bool_option("intervals"))
    {
      domain = new ait<interval_domaint>();
    }
#if 0
    // Not actually implemented, despite the option...
    else if(options.get_bool_option("non-null"))
    {
      domain=new ait<non_null_domaint>();
    }
#endif
  }
  else if(options.get_bool_option("concurrent"))
  {
#if 0
    // Disabled until merge_shared is implemented for these
    if(options.get_bool_option("constants"))
    {
      domain=new concurrency_aware_ait<constant_propagator_domaint>();
    }
    else if(options.get_bool_option("dependence-graph"))
    {
      domain=new dependence_grapht(ns);
    }
    else if(options.get_bool_option("intervals"))
    {
      domain=new concurrency_aware_ait<interval_domaint>();
    }
#if 0
    // Not actually implemented, despite the option...
    else if(options.get_bool_option("non-null"))
    {
      domain=new concurrency_aware_ait<non_null_domaint>();
    }
#endif
#endif
  }

  return domain;
}

/// invoke main modules
int janalyzer_parse_optionst::doit()
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

  log_version_and_architecture("JANALYZER");

  register_languages();

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

  lazy_goto_modelt lazy_goto_model =
    lazy_goto_modelt::from_handler_object(*this, options, ui_message_handler);
  lazy_goto_model.initialize(cmdline.args, options);

  class_hierarchy =
    util_make_unique<class_hierarchyt>(lazy_goto_model.symbol_table);

  log.status() << "Generating GOTO Program" << messaget::eom;
  lazy_goto_model.load_all_functions();

  std::unique_ptr<abstract_goto_modelt> goto_model_ptr =
    lazy_goto_modelt::process_whole_model_and_freeze(
      std::move(lazy_goto_model));
  if(goto_model_ptr == nullptr)
    return CPROVER_EXIT_INTERNAL_ERROR;

  goto_modelt &goto_model = dynamic_cast<goto_modelt &>(*goto_model_ptr);

  // show it?
  if(cmdline.isset("show-symbol-table"))
  {
    ::show_symbol_table(goto_model.symbol_table, ui_message_handler);
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

  return perform_analysis(goto_model, options);
}

/// Depending on the command line mode, run one of the analysis tasks
int janalyzer_parse_optionst::perform_analysis(
  goto_modelt &goto_model,
  const optionst &options)
{
  if(options.get_bool_option("taint"))
  {
    std::string taint_file = cmdline.get_value("taint");

    if(cmdline.isset("show-taint"))
    {
      taint_analysis(goto_model, taint_file, ui_message_handler, true);
      return CPROVER_EXIT_SUCCESS;
    }
    else
    {
      optionalt<std::string> json_file;
      if(cmdline.isset("json"))
        json_file = cmdline.get_value("json");
      bool result = taint_analysis(
        goto_model, taint_file, ui_message_handler, false, json_file);
      return result ? CPROVER_EXIT_VERIFICATION_UNSAFE : CPROVER_EXIT_SUCCESS;
    }
  }

  // If no domain is given, this lightweight version of the analysis is used.
  if(
    options.get_bool_option("unreachable-instructions") &&
    options.get_bool_option("specific-analysis"))
  {
    const std::string json_file = cmdline.get_value("json");

    if(json_file.empty())
      unreachable_instructions(goto_model, false, std::cout);
    else if(json_file == "-")
      unreachable_instructions(goto_model, true, std::cout);
    else
    {
      std::ofstream ofs(json_file);
      if(!ofs)
      {
        log.error() << "Failed to open json output '" << json_file << "'"
                    << messaget::eom;
        return CPROVER_EXIT_INTERNAL_ERROR;
      }

      unreachable_instructions(goto_model, true, ofs);
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    options.get_bool_option("unreachable-functions") &&
    options.get_bool_option("specific-analysis"))
  {
    const std::string json_file = cmdline.get_value("json");

    if(json_file.empty())
      unreachable_functions(goto_model, false, std::cout);
    else if(json_file == "-")
      unreachable_functions(goto_model, true, std::cout);
    else
    {
      std::ofstream ofs(json_file);
      if(!ofs)
      {
        log.error() << "Failed to open json output '" << json_file << "'"
                    << messaget::eom;
        return CPROVER_EXIT_INTERNAL_ERROR;
      }

      unreachable_functions(goto_model, true, ofs);
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    options.get_bool_option("reachable-functions") &&
    options.get_bool_option("specific-analysis"))
  {
    const std::string json_file = cmdline.get_value("json");

    if(json_file.empty())
      reachable_functions(goto_model, false, std::cout);
    else if(json_file == "-")
      reachable_functions(goto_model, true, std::cout);
    else
    {
      std::ofstream ofs(json_file);
      if(!ofs)
      {
        log.error() << "Failed to open json output '" << json_file << "'"
                    << messaget::eom;
        return CPROVER_EXIT_INTERNAL_ERROR;
      }

      reachable_functions(goto_model, true, ofs);
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(options.get_bool_option("show-local-may-alias"))
  {
    namespacet ns(goto_model.symbol_table);

    for(const auto &gf_entry : goto_model.goto_functions.function_map)
    {
      std::cout << ">>>>\n";
      std::cout << ">>>> " << gf_entry.first << '\n';
      std::cout << ">>>>\n";
      local_may_aliast local_may_alias(gf_entry.second);
      local_may_alias.output(std::cout, gf_entry.second, ns);
      std::cout << '\n';
    }

    return CPROVER_EXIT_SUCCESS;
  }

  label_properties(goto_model);

  if(cmdline.isset("show-properties"))
  {
    show_properties(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("property"))
    ::set_properties(goto_model, cmdline.get_values("property"));

  if(options.get_bool_option("general-analysis"))
  {
    // Output file factory
    const std::string outfile = options.get_option("outfile");
    std::ofstream output_stream;
    if(!(outfile == "-"))
      output_stream.open(outfile);

    std::ostream &out((outfile == "-") ? std::cout : output_stream);

    if(!out)
    {
      log.error() << "Failed to open output file '" << outfile << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    // Build analyzer
    log.status() << "Selecting abstract domain" << messaget::eom;
    namespacet ns(goto_model.symbol_table); // Must live as long as the domain.
    std::unique_ptr<ai_baset> analyzer(build_analyzer(goto_model, options, ns));

    if(analyzer == nullptr)
    {
      log.status() << "Task / Interpreter / Domain combination not supported"
                   << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    // Run
    log.status() << "Computing abstract states" << messaget::eom;
    (*analyzer)(goto_model);

    // Perform the task
    log.status() << "Performing task" << messaget::eom;
    bool result = true;
    if(options.get_bool_option("show"))
    {
      static_show_domain(goto_model, *analyzer, options, out);
      return CPROVER_EXIT_SUCCESS;
    }
    else if(options.get_bool_option("verify"))
    {
      result = static_verifier(
        goto_model, *analyzer, options, ui_message_handler, out);
    }
    else if(options.get_bool_option("simplify"))
    {
      result = static_simplifier(
        goto_model, *analyzer, options, ui_message_handler, out);
    }
    else if(options.get_bool_option("unreachable-instructions"))
    {
      result = static_unreachable_instructions(
        goto_model, *analyzer, options, out);
    }
    else if(options.get_bool_option("unreachable-functions"))
    {
      result = static_unreachable_functions(
        goto_model, *analyzer, options, out);
    }
    else if(options.get_bool_option("reachable-functions"))
    {
      result = static_reachable_functions(
        goto_model, *analyzer, options, out);
    }
    else
    {
      log.error() << "Unhandled task" << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    return result ? CPROVER_EXIT_VERIFICATION_UNSAFE
                  : CPROVER_EXIT_VERIFICATION_SAFE;
  }

  // Final defensive error case
  log.error() << "no analysis option given -- consider reading --help"
              << messaget::eom;
  return CPROVER_EXIT_USAGE_ERROR;
}

bool janalyzer_parse_optionst::process_goto_functions(
  goto_modelt &goto_model,
  const optionst &options)
{
  log.status() << "Running GOTO functions transformation passes"
               << messaget::eom;

  // remove catch and throw
  remove_exceptions(goto_model, *class_hierarchy.get(), ui_message_handler);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // remove skips such that trivial GOTOs are deleted
  remove_skip(goto_model);

  // label the assertions
  // This must be done after adding assertions and
  // before using the argument of the "property" option.
  // Do not re-label after using the property slicer because
  // this would cause the property identifiers to change.
  label_properties(goto_model);

  return false;
}

void janalyzer_parse_optionst::process_goto_function(
  goto_model_functiont &function,
  const abstract_goto_modelt &model,
  const optionst &options)
{
  journalling_symbol_tablet &symbol_table = function.get_symbol_table();
  namespacet ns(symbol_table);
  goto_functionst::goto_functiont &goto_function = function.get_goto_function();

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

  transform_assertions_assumptions(options, function.get_goto_function().body);
}

bool janalyzer_parse_optionst::can_generate_function_body(const irep_idt &name)
{
  static const irep_idt initialize_id = INITIALIZE_FUNCTION;

  return name != goto_functionst::entry_point() && name != initialize_id;
}

bool janalyzer_parse_optionst::generate_function_body(
  const irep_idt &function_name,
  symbol_table_baset &symbol_table,
  goto_functiont &function,
  bool body_available)
{
  return false;
}

/// display command line help
void janalyzer_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("JANALYZER", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2016-2018") << '\n'
            << align_center_with_border("Daniel Kroening, Diffblue") << '\n'
            << align_center_with_border("kroening@kroening.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " janalyzer [-?] [-h] [--help] show help\n"
    " janalyzer\n"
    HELP_JAVA_METHOD_NAME
    " janalyzer\n"
    HELP_JAVA_CLASS_NAME
    " janalyzer\n"
    HELP_JAVA_JAR
    " janalyzer\n"
    HELP_JAVA_GOTO_BINARY
    "\n"
    HELP_JAVA_CLASSPATH
    HELP_FUNCTIONS
    "\n"
    "Task options:\n"
    " --show                       display the abstract domains\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --verify                     use the abstract domains to check assertions\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --simplify file_name         use the abstract domains to simplify the program\n"
    " --unreachable-instructions   list dead code\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --unreachable-functions      list functions unreachable from the entry point\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --reachable-functions        list functions reachable from the entry point\n"
    "\n"
    "Abstract interpreter options:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --location-sensitive         use location-sensitive abstract interpreter\n"
    " --concurrent                 use concurrency-aware abstract interpreter\n"
    "\n"
    "Domain options:\n"
    " --constants                  constant domain\n"
    " --intervals                  interval domain\n"
    " --non-null                   non-null domain\n"
    " --dependence-graph           data and control dependencies between instructions\n" // NOLINT(*)
    "\n"
    "Output options:\n"
    " --text file_name             output results in plain text to given file\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --json file_name             output results in JSON format to given file\n"
    " --xml file_name              output results in XML format to given file\n"
    " --dot file_name              output results in DOT format to given file\n"
    "\n"
    "Specific analyses:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --taint file_name            perform taint analysis using rules in given file\n"
    "\n"
    "Java Bytecode frontend options:\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_SHOW_PROPERTIES
    "\n"
    "Program instrumentation options:\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
