/*******************************************************************\

Module: Goto-Analyzer Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto-Analyser Command Line Option Processing

#include "goto_analyzer_parse_options.h"

#include <cstdlib> // exit()
#include <fstream>
#include <iostream>
#include <memory>

#include <ansi-c/cprover_library.h>

#include <assembler/remove_asm.h>

#include <cpp/cprover_library.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <analyses/ai.h>
#include <analyses/local_may_alias.h>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/version.h>

#include "build_analyzer.h"
#include "show_on_source.h"
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

void goto_analyzer_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // The user should either select:
  //  1. a specific analysis, or
  //  2. a tuple of task / analyser options / outputs

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
    // Abstract interpreter choice
    if(cmdline.isset("recursive-interprocedural"))
      options.set_option("recursive-interprocedural", true);
    else if(cmdline.isset("three-way-merge"))
      options.set_option("three-way-merge", true);
    else if(cmdline.isset("legacy-ait") || cmdline.isset("location-sensitive"))
    {
      options.set_option("legacy-ait", true);
      // Fixes a number of other options as well
      options.set_option("ahistorical", true);
      options.set_option("history set", true);
      options.set_option("one-domain-per-location", true);
      options.set_option("storage set", true);
    }
    else if(cmdline.isset("legacy-concurrent") || cmdline.isset("concurrent"))
    {
      options.set_option("legacy-concurrent", true);
      options.set_option("ahistorical", true);
      options.set_option("history set", true);
      options.set_option("one-domain-per-location", true);
      options.set_option("storage set", true);
    }
    else
    {
      // Silently default to legacy-ait for backwards compatability
      options.set_option("legacy-ait", true);
      // Fixes a number of other options as well
      options.set_option("ahistorical", true);
      options.set_option("history set", true);
      options.set_option("one-domain-per-location", true);
      options.set_option("storage set", true);
    }

    // History choice
    if(cmdline.isset("ahistorical"))
    {
      options.set_option("ahistorical", true);
      options.set_option("history set", true);
    }
    else if(cmdline.isset("call-stack"))
    {
      options.set_option("call-stack", true);
      options.set_option(
        "call-stack-recursion-limit", cmdline.get_value("call-stack"));
      options.set_option("history set", true);
    }
    else if(cmdline.isset("loop-unwind"))
    {
      options.set_option("local-control-flow-history", true);
      options.set_option("local-control-flow-history-forward", false);
      options.set_option("local-control-flow-history-backward", true);
      options.set_option(
        "local-control-flow-history-limit", cmdline.get_value("loop-unwind"));
      options.set_option("history set", true);
    }
    else if(cmdline.isset("branching"))
    {
      options.set_option("local-control-flow-history", true);
      options.set_option("local-control-flow-history-forward", true);
      options.set_option("local-control-flow-history-backward", false);
      options.set_option(
        "local-control-flow-history-limit", cmdline.get_value("branching"));
      options.set_option("history set", true);
    }
    else if(cmdline.isset("loop-unwind-and-branching"))
    {
      options.set_option("local-control-flow-history", true);
      options.set_option("local-control-flow-history-forward", true);
      options.set_option("local-control-flow-history-backward", true);
      options.set_option(
        "local-control-flow-history-limit",
        cmdline.get_value("loop-unwind-and-branching"));
      options.set_option("history set", true);
    }

    if(!options.get_bool_option("history set"))
    {
      // Default to ahistorical as it is the expected for of analysis
      log.status() << "History not specified, defaulting to --ahistorical"
                   << messaget::eom;
      options.set_option("ahistorical", true);
      options.set_option("history set", true);
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
    else if(cmdline.isset("vsd") || cmdline.isset("variable-sensitivity"))
    {
      options.set_option("vsd", true);
      options.set_option("domain set", true);

      PARSE_OPTIONS_VSD(cmdline, options);
    }
    else if(cmdline.isset("dependence-graph-vs"))
    {
      options.set_option("dependence-graph-vs", true);
      options.set_option("domain set", true);

      PARSE_OPTIONS_VSD(cmdline, options);
      options.set_option("data-dependencies", true); // Always set
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

  // Storage choice
  if(cmdline.isset("one-domain-per-history"))
  {
    options.set_option("one-domain-per-history", true);
    options.set_option("storage set", true);
  }
  else if(cmdline.isset("one-domain-per-location"))
  {
    options.set_option("one-domain-per-location", true);
    options.set_option("storage set", true);
  }

  if(!options.get_bool_option("storage set"))
  {
    // one-domain-per-location and one-domain-per-history are effectively
    // the same when using ahistorical so we default to per-history so that
    // more sophisticated history objects work as expected
    log.status() << "Storage not specified,"
                 << " defaulting to --one-domain-per-history" << messaget::eom;
    options.set_option("one-domain-per-history", true);
    options.set_option("storage set", true);
  }

  if(cmdline.isset("validate-goto-model"))
  {
    options.set_option("validate-goto-model", true);
  }
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

  log_version_and_architecture("GOTO-ANALYZER");

  register_languages();

  goto_model = initialize_goto_model(cmdline.args, ui_message_handler, options);

  // Preserve backwards compatibility in processing
  options.set_option("partial-inline", true);
  options.set_option("rewrite-union", false);
  options.set_option("remove-returns", true);

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
    std::unique_ptr<ai_baset> analyzer;

    try
    {
      analyzer = build_analyzer(options, goto_model, ns, ui_message_handler);
    }
    catch(const invalid_command_line_argument_exceptiont &e)
    {
      log.error() << e.what() << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }

    if(analyzer == nullptr)
    {
      log.status() << "Task / Interpreter combination not supported"
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
  // Remove inline assembler; this needs to happen before
  // adding the library.
  remove_asm(goto_model);

  // add the library
  log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(goto_model, ui_message_handler, cprover_cpp_library_factory);
  link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);

  // Common removal of types and complex constructs
  if(::process_goto_program(goto_model, options, log))
    return true;

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
    " --recursive-interprocedural  use recursion to handle interprocedural reasoning\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --three-way-merge            use VSD's three-way merge on return from function call\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --legacy-ait                 recursion for function and one domain per location\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --legacy-concurrent          legacy-ait with an extended fixed-point for concurrency\n"
    "\n"
    "History options:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --ahistorical                the most basic history, tracks locations only\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --call-stack n               track the calling location stack for each function\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    "                              limiting to at most n recursive loops, 0 to disable\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --loop-unwind n              track the number of loop iterations within a function\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    "                              limited to n histories per location, 0 is unlimited\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --branching n                track the forwards jumps (if, switch, etc.) within a function\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    "                              limited to n histories per location, 0 is unlimited\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --loop-unwind-and-branching n track all local control flow\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    "                              limited to n histories per location, 0 is unlimited\n"
    "\n"
    "Domain options:\n"
    " --constants                  a constant for each variable if possible\n"
    " --intervals                  an interval for each variable\n"
    " --non-null                   tracks which pointers are non-null\n"
    " --dependence-graph           data and control dependencies between instructions\n" // NOLINT(*)
    " --vsd                        a configurable non-relational domain\n" // NOLINT(*)
    " --dependence-graph-vs        dependencies between instructions using VSD\n" // NOLINT(*)
    "\n"
    "Variable sensitivity domain (VSD) options:\n"
    HELP_VSD
    "\n"
    "Storage options:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --one-domain-per-history     stores a domain for each history object created\n"
    " --one-domain-per-location    stores a domain for each location reached\n"
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
    HELP_CONFIG_C_CPP
    HELP_FUNCTIONS
    "\n"
    "Platform options:\n"
    HELP_CONFIG_PLATFORM
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_SHOW_PROPERTIES
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    HELP_CONFIG_LIBRARY
    "\n"
    "Other options:\n"
    HELP_VALIDATE
    " --version                    show version and exit\n"
    HELP_FLUSH
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
