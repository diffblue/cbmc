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
#include <java_bytecode/java_bytecode_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <analyses/constant_propagator.h>
#include <analyses/dependence_graph.h>
#include <analyses/goto_check.h>
#include <analyses/interval_domain.h>
#include <analyses/is_threaded.h>
#include <analyses/local_may_alias.h>

#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-analyzer/static_show_domain.h>
#include <goto-analyzer/static_simplifier.h>
#include <goto-analyzer/static_verifier.h>
#include <goto-analyzer/taint_analysis.h>
#include <goto-analyzer/unreachable_instructions.h>

janalyzer_parse_optionst::janalyzer_parse_optionst(int argc, const char **argv)
  : parse_options_baset(JANALYZER_OPTIONS, argc, argv),
    messaget(ui_message_handler),
    ui_message_handler(cmdline, std::string("JANALYZER ") + CBMC_VERSION)
{
}

void janalyzer_parse_optionst::register_languages()
{
  register_language(new_java_bytecode_language);
}

void janalyzer_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

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

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_values("error-label"));

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
        status() << "Domain not specified, defaulting to --constants" << eom;
        options.set_option("constants", true);
      }
    }
  }
}

/// For the task, build the appropriate kind of analyzer
/// Ideally this should be a pure function of options.
/// However at the moment some domains require the goto_model
ai_baset *janalyzer_parse_optionst::build_analyzer(
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
  eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  //
  // Print a banner
  //
  status() << "JANALYZER version " << CBMC_VERSION << " " << sizeof(void *) * 8
           << "-bit " << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  register_languages();

  try
  {
    goto_model = initialize_goto_model(cmdline, get_message_handler(), options);
  }

  catch(const char *e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(int e)
  {
    error() << "Numeric exception: " << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  if(process_goto_program(options))
    return CPROVER_EXIT_INTERNAL_ERROR;

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
      goto_model,
      get_message_handler(),
      get_ui(),
      cmdline.isset("list-goto-functions"));
    return CPROVER_EXIT_SUCCESS;
  }

  try
  {
    return perform_analysis(options);
  }

  catch(const char *e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(int e)
  {
    error() << "Numeric exception: " << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }
}

/// Depending on the command line mode, run one of the analysis tasks
int janalyzer_parse_optionst::perform_analysis(const optionst &options)
{
  if(options.get_bool_option("taint"))
  {
    std::string taint_file = cmdline.get_value("taint");

    if(cmdline.isset("show-taint"))
    {
      taint_analysis(goto_model, taint_file, get_message_handler(), true, "");
      return CPROVER_EXIT_SUCCESS;
    }
    else
    {
      std::string json_file = cmdline.get_value("json");
      bool result = taint_analysis(
        goto_model, taint_file, get_message_handler(), false, json_file);
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
        error() << "Failed to open json output `" << json_file << "'" << eom;
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
        error() << "Failed to open json output `" << json_file << "'" << eom;
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
        error() << "Failed to open json output `" << json_file << "'" << eom;
        return CPROVER_EXIT_INTERNAL_ERROR;
      }

      reachable_functions(goto_model, true, ofs);
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(options.get_bool_option("show-local-may-alias"))
  {
    namespacet ns(goto_model.symbol_table);

    forall_goto_functions(it, goto_model.goto_functions)
    {
      std::cout << ">>>>\n";
      std::cout << ">>>> " << it->first << '\n';
      std::cout << ">>>>\n";
      local_may_aliast local_may_alias(it->second);
      local_may_alias.output(std::cout, it->second, ns);
      std::cout << '\n';
    }

    return CPROVER_EXIT_SUCCESS;
  }

  label_properties(goto_model);

  if(cmdline.isset("show-properties"))
  {
    show_properties(goto_model, get_message_handler(), get_ui());
    return CPROVER_EXIT_SUCCESS;
  }

  if(set_properties())
    return CPROVER_EXIT_SET_PROPERTIES_FAILED;

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
      error() << "Failed to open output file `" << outfile << "'" << eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    // Build analyzer
    status() << "Selecting abstract domain" << eom;
    namespacet ns(goto_model.symbol_table); // Must live as long as the domain.
    std::unique_ptr<ai_baset> analyzer(build_analyzer(options, ns));

    if(analyzer == nullptr)
    {
      status() << "Task / Interpreter / Domain combination not supported"
               << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    // Run
    status() << "Computing abstract states" << eom;
    (*analyzer)(goto_model);

    // Perform the task
    status() << "Performing task" << eom;
    bool result = true;
    if(options.get_bool_option("show"))
    {
      result = static_show_domain(
        goto_model, *analyzer, options, out);
    }
    else if(options.get_bool_option("verify"))
    {
      result = static_verifier(
        goto_model, *analyzer, options, get_message_handler(), out);
    }
    else if(options.get_bool_option("simplify"))
    {
      result = static_simplifier(
        goto_model, *analyzer, options, get_message_handler(), out);
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
      error() << "Unhandled task" << eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    return result ? CPROVER_EXIT_VERIFICATION_UNSAFE
                  : CPROVER_EXIT_VERIFICATION_SAFE;
  }

  // Final defensive error case
  error() << "no analysis option given -- consider reading --help" << eom;
  return CPROVER_EXIT_USAGE_ERROR;
}

bool janalyzer_parse_optionst::set_properties()
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

bool janalyzer_parse_optionst::process_goto_program(const optionst &options)
{
  try
  {
    // remove function pointers
    status() << "Removing function pointers and virtual functions" << eom;
    remove_function_pointers(
      get_message_handler(), goto_model, cmdline.isset("pointer-check"));
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(goto_model);
    // remove Java throw and catch
    // This introduces instanceof, so order is important:
    remove_exceptions(goto_model, get_message_handler());
    // remove rtti
    remove_instanceof(goto_model, get_message_handler());

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_model, ui_message_handler);

    // remove returns, gcc vectors, complex
    remove_returns(goto_model);
    remove_vector(goto_model);
    remove_complex(goto_model);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();
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

/// display command line help
void janalyzer_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("JANALYZER", CBMC_VERSION) << '\n'
            <<
     /* NOLINTNEXTLINE(whitespace/line_length) */
    "* *                   Copyright (C) 2016-2018                    * *\n"
    "* *                  Daniel Kroening, Diffblue                   * *\n"
    "* *                   kroening@kroening.com                      * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " janalyzer [-?] [-h] [--help] show help\n"
    " janalyzer class              name of class or JAR file to be checked\n"
    "                              In the case of a JAR file, if a main class can be\n" // NOLINT(*)
    "                              inferred from --main-class, --function, or the JAR\n" // NOLINT(*)
    "                              manifest (checked in this order), the behavior is\n" // NOLINT(*)
    "                              the same as running janalyzer on the corresponding\n" // NOLINT(*)
    "                              class file."
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
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    HELP_FUNCTIONS
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_SHOW_PROPERTIES
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
