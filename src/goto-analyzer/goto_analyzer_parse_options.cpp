/*******************************************************************\

Module: Goto-Analyzer Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto-Analyser Command Line Option Processing

#include "goto_analyzer_parse_options.h"

#include <cstdlib> // exit()
#include <iostream>
#include <fstream>
#include <memory>
#include <string>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/cprover_library.h>

#include <assembler/remove_asm.h>

#include <cpp/cpp_language.h>
#include <cpp/cprover_library.h>

#include <jsil/jsil_language.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/label_function_pointer_call_sites.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/validate_goto_model.h>

#include <analyses/is_threaded.h>
#include <analyses/goto_check.h>
#include <analyses/local_may_alias.h>
#include <analyses/constant_propagator.h>
#include <analyses/dependence_graph.h>
#include <analyses/interval_domain.h>
#include <analyses/variable-sensitivity/variable_sensitivity_dependence_graph.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <langapi/mode.h>
#include <langapi/language.h>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/unicode.h>
#include <util/version.h>

#include "show_on_source.h"
#include "show_function_pointer_values.h"
#include "static_show_domain.h"
#include "static_simplifier.h"
#include "static_verifier.h"
#include "taint_analysis.h"
#include "unreachable_instructions.h"

goto_analyzer_parse_optionst::goto_analyzer_parse_optionst(
  int argc,
  const char **argv)
  : parse_options_baset(
      GOTO_ANALYSER_OPTIONS,
      argc,
      argv,
      std::string("GOTO-ANALYZER "))
{
}

void goto_analyzer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  register_language(new_jsil_language);
}

void goto_analyzer_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

#if 0
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
#endif

#if 0
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
#endif

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
  else if(cmdline.isset("show-on-source"))
  {
    options.set_option("show-on-source", true);
    options.set_option("general-analysis", true);
  }
  else if(cmdline.isset("verify"))
  {
    options.set_option("verify", true);
    options.set_option("general-analysis", true);
  }
  else if(cmdline.isset("simplify"))
  {
    if(cmdline.get_value("simplify") == "-")
      throw invalid_command_line_argument_exceptiont(
        "cannot output goto binary to stdout", "--simplify");

    options.set_option("simplify", true);
    options.set_option("outfile", cmdline.get_value("simplify"));
    options.set_option("general-analysis", true);

    // For development allow slicing to be disabled in the simplify task
    options.set_option(
      "simplify-slicing",
      !(cmdline.isset("no-simplify-slicing")));
  }
  else if(cmdline.isset("show-intervals"))
  {
    // For backwards compatibility
    options.set_option("show", true);
    options.set_option("general-analysis", true);
    options.set_option("intervals", true);
    options.set_option("domain set", true);
  }
  else if(cmdline.isset("show-non-null"))
  {
    // For backwards compatibility
    options.set_option("show", true);
    options.set_option("general-analysis", true);
    options.set_option("non-null", true);
    options.set_option("domain set", true);
  }
  else if(cmdline.isset("intervals") || cmdline.isset("non-null"))
  {
    // Partial backwards compatability, just giving these domains without
    // a task will work.  However it will use the general default of verify
    // rather than their historical default of show.
    options.set_option("verify", true);
    options.set_option("general-analysis", true);
  }

  if(options.get_bool_option("general-analysis") || reachability_task)
  {
    options.set_option("vs-progress", cmdline.isset("vs-progress"));
    options.set_option(
      "vs-progress-memory-usage", cmdline.isset("vs-progress-memory-usage"));
    #ifndef USE_STD_STRING
    options.set_option(
      "vs-progress-string-statistics", cmdline.isset("vs-progress-string-statistics"));
    #endif
    const char *vs_progress_interval = "vs-progress-interval";

    if(cmdline.isset(vs_progress_interval))
    {
      std::string interval_value = cmdline.get_value(vs_progress_interval);

      try
      {
        // check if valid float
        std::stof(interval_value);
      }
      catch(std::out_of_range)
      {
        throw "argument to --vs-progress-interval out of range";
      }
      catch(std::invalid_argument)
      {
        throw "argument to --vs-progress-interval is invalid";
      }

      options.set_option(vs_progress_interval, interval_value);
    }

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
    // "variable" is deprecated but still supported
    else if(cmdline.isset("variable") || cmdline.isset("variable-sensitivity"))
    {
      options.set_option("variable-sensitivity", true);
      options.set_option("domain set", true);

      // Configuration of variable sensitivity
      options.set_option("pointers", cmdline.isset("pointers"));
      options.set_option("arrays", cmdline.isset("arrays"));
      options.set_option("structs", cmdline.isset("structs"));
      options.set_option("data-dependencies", cmdline.isset("data-dependencies"));
      options.set_option("interval", cmdline.isset("interval-values"));
      options.set_option("value-set", cmdline.isset("value-set"));
      if(cmdline.isset("get-fp-values")) {
        options.set_option("function-pointer-values", cmdline.get_value("get-fp-values"));
      }
    }
    else if(cmdline.isset("dependence-graph-vs"))
    {
      options.set_option("dependence-graph-vs", true);
      options.set_option("domain set", true);

      // Configuration of variable sensitivity domain
      options.set_option("pointers", cmdline.isset("pointers"));
      options.set_option("arrays", cmdline.isset("arrays"));
      options.set_option("structs", cmdline.isset("structs"));
      options.set_option("data-dependencies", true);
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

  if(cmdline.isset("validate-goto-model"))
  {
    options.set_option("validate-goto-model", true);
  }
}

/// For the task, build the appropriate kind of analyzer
/// Ideally this should be a pure function of options.
/// However at the moment some domains require the goto_model
ai_baset *goto_analyzer_parse_optionst::build_analyzer(
  const optionst &options,
  const namespacet &ns)
{
  ai_baset *domain = nullptr;

  if(options.get_bool_option("location-sensitive"))
  {
    if(options.get_bool_option("constants"))
    {
      // constant_propagator_ait derives from ait<constant_propagator_domaint>
      domain=new constant_propagator_ait(goto_model.goto_functions);
    }
    else if(options.get_bool_option("dependence-graph"))
    {
      domain=new dependence_grapht(ns);
    }
    else if(options.get_bool_option("intervals"))
    {
      domain=new ait<interval_domaint>();
    }
#if 0
    // Not actually implemented, despite the option...
    else if(options.get_bool_option("non-null"))
    {
      domain=new ait<non_null_domaint>();
    }
#endif
    else if(options.get_bool_option("variable-sensitivity"))
    {
      domain = new ait<variable_sensitivity_domaint>(
        ai_configt::from_options(options));
    }
    else if(options.get_bool_option("dependence-graph-vs"))
    {
      domain = new variable_sensitivity_dependence_grapht(
        goto_model.goto_functions, ns, ai_configt::from_options(options));
    }
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
    else if(options.get_bool_option("variable-sensitivity"))
    {
      domain=new concurrency_aware_ait<variable_sensitivity_domaint>();
    }
#endif
  }

  return domain;
}

/// invoke main modules
int goto_analyzer_parse_optionst::doit()
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

  //
  // Print a banner
  //
  log.status() << "GOTO-ANALYSER version " << CBMC_VERSION << " "
               << sizeof(void *) * 8 << "-bit " << config.this_architecture()
               << " " << config.this_operating_system() << messaget::eom;

  register_languages();

  goto_model = initialize_goto_model(cmdline.args, ui_message_handler, options);

  if(process_goto_program(options))
    return CPROVER_EXIT_INTERNAL_ERROR;

  if(cmdline.isset("validate-goto-model"))
  {
    goto_model.validate();
  }

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

  return perform_analysis(options);
}


/// Depending on the command line mode, run one of the analysis tasks
int goto_analyzer_parse_optionst::perform_analysis(const optionst &options)
{
  adjust_float_expressions(goto_model);
  if(options.get_bool_option("taint"))
  {
    std::string taint_file=cmdline.get_value("taint");

    if(cmdline.isset("show-taint"))
    {
      taint_analysis(goto_model, taint_file, ui_message_handler, true);
      return CPROVER_EXIT_SUCCESS;
    }
    else
    {
      std::string json_file=cmdline.get_value("json");
      bool result = taint_analysis(
        goto_model, taint_file, ui_message_handler, false, json_file);
      return result ? CPROVER_EXIT_VERIFICATION_UNSAFE : CPROVER_EXIT_SUCCESS;
    }
  }

  // If no domain is given, this lightweight version of the analysis is used.
  if(options.get_bool_option("unreachable-instructions") &&
     options.get_bool_option("specific-analysis"))
  {
    const std::string json_file=cmdline.get_value("json");

    if(json_file.empty())
      unreachable_instructions(goto_model, false, std::cout);
    else if(json_file=="-")
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

  if(options.get_bool_option("unreachable-functions") &&
     options.get_bool_option("specific-analysis"))
  {
    const std::string json_file=cmdline.get_value("json");

    if(json_file.empty())
      unreachable_functions(goto_model, false, std::cout);
    else if(json_file=="-")
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

  if(options.get_bool_option("reachable-functions") &&
     options.get_bool_option("specific-analysis"))
  {
    const std::string json_file=cmdline.get_value("json");

    if(json_file.empty())
      reachable_functions(goto_model, false, std::cout);
    else if(json_file=="-")
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
    show_properties(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("property"))
    ::set_properties(goto_model, cmdline.get_values("property"));

  if(options.get_bool_option("general-analysis"))
  {
    // Store options in static variable_sensitivity_object_factory object
    try
    {
      variable_sensitivity_object_factoryt::instance().set_options(
        vsd_configt::from_options(options));
    }
    catch(const invalid_command_line_argument_exceptiont &e)
    {
      log.error() << e.what() << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }

    // Output file factory
    const std::string outfile=options.get_option("outfile");

    std::ofstream output_stream;
    if(outfile != "-" && !outfile.empty())
      output_stream.open(outfile);

    std::ostream &out(
      (outfile == "-" || outfile.empty()) ? std::cout : output_stream);

    if(!out)
    {
      log.error() << "Failed to open output file '" << outfile << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    // Build analyzer
    log.status() << "Selecting abstract domain" << messaget::eom;
    namespacet ns(goto_model.symbol_table);  // Must live as long as the domain.
    std::unique_ptr<ai_baset> analyzer(build_analyzer(options, ns));

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
    else if(options.get_bool_option("show-on-source"))
    {
      show_on_source(goto_model, *analyzer, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }
    else if(options.is_set("function-pointer-values"))
    {
      std::string filename = options.get_option("function-pointer-values");
      print_function_pointer_values(goto_model, *analyzer, options, ui_message_handler, filename);
      return CPROVER_EXIT_SUCCESS;
    }
    else if(options.get_bool_option("verify"))
    {
      result = static_verifier(
        goto_model, *analyzer, options, ui_message_handler, out);
    }
    else if(options.get_bool_option("simplify"))
    {
      PRECONDITION(!outfile.empty() && outfile != "-");
      output_stream.close();
      output_stream.open(outfile, std::ios::binary);
      result = static_simplifier(
        goto_model, *analyzer, options, ui_message_handler, out);
    }
    else if(options.get_bool_option("unreachable-instructions"))
    {
      result = static_unreachable_instructions(goto_model,
                                               *analyzer,
                                               options,
                                               out);
    }
    else if(options.get_bool_option("unreachable-functions"))
    {
      result = static_unreachable_functions(goto_model,
                                            *analyzer,
                                            options,
                                            out);
    }
    else if(options.get_bool_option("reachable-functions"))
    {
      result = static_reachable_functions(goto_model,
                                          *analyzer,
                                          options,
                                          out);
    }
    else
    {
      log.error() << "Unhandled task" << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }

    return result ?
      CPROVER_EXIT_VERIFICATION_UNSAFE : CPROVER_EXIT_VERIFICATION_SAFE;
  }


  // Final defensive error case
  log.error() << "no analysis option given -- consider reading --help"
              << messaget::eom;
  return CPROVER_EXIT_USAGE_ERROR;
}

bool goto_analyzer_parse_optionst::process_goto_program(
  const optionst &options)
{
  {
    #if 0
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(goto_model);

    // add the library
    log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")" << messaget::eom;
    link_to_library(
      goto_model, ui_message_handler, cprover_cpp_library_factory);
    link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);
    #endif

    if(options.is_set("function-pointer-values")) {
      label_function_pointer_call_sites(goto_model);
    }

    // remove function pointers
    log.status() << "Removing function pointers and virtual functions"
                 << messaget::eom;
    remove_function_pointers(
      ui_message_handler, goto_model, cmdline.isset("pointer-check"));

    // do partial inlining
    log.status() << "Partial Inlining" << messaget::eom;
    goto_partial_inline(goto_model, ui_message_handler);

    // remove returns, gcc vectors, complex
    remove_returns(goto_model);
    remove_vector(goto_model);
    remove_complex(goto_model);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();
  }
  return false;
}

/// display command line help
void goto_analyzer_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("GOTO-ANALYZER", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2017-2018") << '\n'
            << align_center_with_border("Daniel Kroening, Diffblue") << '\n'
            << align_center_with_border("kroening@kroening.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-analyzer [-h] [--help]  show help\n"
    " goto-analyzer file.c ...     source file names\n"
    "\n"
    "Task options:\n"
    " --show                       display the abstract states on the goto program\n" // NOLINT(*)
    " --show-on-source             display the abstract states on the source\n"
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
    " --dependence-graph-vs        data dependencies between instructions using variable sensitivity\n" // NOLINT(*)
    " --variable-sensitivity       a highly configurable non-relational domain\n" // NOLINT(*)
    " --vs-progress                print variable sensitivity progress data\n"
    " --vs-progress-interval       minimum interval (in s) between progress reports\n" // NOLINT(*)
    " --vs-progress-memory-usage   display variable sensitivity memory usage along progress\n" // NOLINT(*)
    #ifndef USE_STD_STRING
    " --vs-progress-string-statistics  display string container statistics along progress\n" // NOLINT(*)
    #else
    " --vs-progress-string-statistics  (not available because goto-analyzer was compiled with USE_STD_STRING)"
    #endif
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
    "C/C++ frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --arch X                     set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    " --c89/99/11                  set C language standard (default: "
                                   << (configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C89?"c89":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C99?"c99":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C11?
                                         "c11":"") << ")\n"
    " --cpp98/03/11                set C++ language standard (default: "
                                   << (configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP98?
                                         "cpp98":
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP03?
                                         "cpp03":
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP11?
                                         "cpp11":"") << ")\n"
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-library                 disable built-in abstract C library\n"
    "\n"
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
    HELP_VALIDATE
    " --version                    show version and exit\n"
    HELP_FLUSH
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
