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

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/cprover_library.h>

#include <assembler/remove_asm.h>

#include <cpp/cpp_language.h>
#include <cpp/cprover_library.h>

#include <jsil/jsil_language.h>

#include <goto-programs/add_malloc_may_fail_variable_initializations.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/validate_goto_model.h>

#include <analyses/call_stack_history.h>
#include <analyses/constant_propagator.h>
#include <analyses/dependence_graph.h>
#include <analyses/goto_check.h>
#include <analyses/interval_domain.h>
#include <analyses/is_threaded.h>
#include <analyses/local_control_flow_history.h>
#include <analyses/local_may_alias.h>
#include <analyses/variable-sensitivity/three_way_merge_abstract_interpreter.h>
#include <analyses/variable-sensitivity/variable_sensitivity_configuration.h>
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
#include "static_show_domain.h"
#include "static_simplifier.h"
#include "static_verifier.h"
#include "taint_analysis.h"
#include "unreachable_instructions.h"

void vsd_options(optionst &options, const cmdlinet &cmdline);

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
      options.set_option(
        "data-dependencies", cmdline.isset("vsd-data-dependencies"));

      vsd_options(options, cmdline);
    }
    else if(cmdline.isset("dependence-graph-vs"))
    {
      options.set_option("dependence-graph-vs", true);
      options.set_option("data-dependencies", true);

      vsd_options(options, cmdline);
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

/// For the task, build the appropriate kind of analyzer
/// Ideally this should be a pure function of options.
/// However at the moment some domains require the goto_model or parts of it
ai_baset *goto_analyzer_parse_optionst::build_analyzer(
  const optionst &options,
  const namespacet &ns)
{
  auto vsd_config = vsd_configt::from_options(options);
  auto vs_object_factory =
    variable_sensitivity_object_factoryt::configured_with(vsd_config);

  // These support all of the option categories
  if(
    options.get_bool_option("recursive-interprocedural") ||
    options.get_bool_option("three-way-merge"))
  {
    // Build the history factory
    std::unique_ptr<ai_history_factory_baset> hf = nullptr;
    if(options.get_bool_option("ahistorical"))
    {
      hf = util_make_unique<
        ai_history_factory_default_constructort<ahistoricalt>>();
    }
    else if(options.get_bool_option("call-stack"))
    {
      hf = util_make_unique<call_stack_history_factoryt>(
        options.get_unsigned_int_option("call-stack-recursion-limit"));
    }
    else if(options.get_bool_option("local-control-flow-history"))
    {
      hf = util_make_unique<local_control_flow_history_factoryt>(
        options.get_bool_option("local-control-flow-history-forward"),
        options.get_bool_option("local-control-flow-history-backward"),
        options.get_unsigned_int_option("local-control-flow-history-limit"));
    }

    // Build the domain factory
    std::unique_ptr<ai_domain_factory_baset> df = nullptr;
    if(options.get_bool_option("constants"))
    {
      df = util_make_unique<
        ai_domain_factory_default_constructort<constant_propagator_domaint>>();
    }
    else if(options.get_bool_option("intervals"))
    {
      df = util_make_unique<
        ai_domain_factory_default_constructort<interval_domaint>>();
    }
    else if(options.get_bool_option("vsd"))
    {
      df = util_make_unique<variable_sensitivity_domain_factoryt>(
        vs_object_factory, vsd_config);
    }
    // non-null is not fully supported, despite the historical options
    // dependency-graph is quite heavily tied to the legacy-ait infrastructure
    // dependency-graph-vs is very similar to dependency-graph

    // Build the storage object
    std::unique_ptr<ai_storage_baset> st = nullptr;
    if(options.get_bool_option("one-domain-per-history"))
    {
      st = util_make_unique<history_sensitive_storaget>();
    }
    else if(options.get_bool_option("one-domain-per-location"))
    {
      st = util_make_unique<location_sensitive_storaget>();
    }

    // Only try to build the abstract interpreter if all the parts have been
    // correctly specified and configured
    if(hf != nullptr && df != nullptr && st != nullptr)
    {
      if(options.get_bool_option("recursive-interprocedural"))
      {
        return new ai_recursive_interproceduralt(
          std::move(hf), std::move(df), std::move(st));
      }
      else if(options.get_bool_option("three-way-merge"))
      {
        // Only works with VSD
        if(options.get_bool_option("vsd"))
        {
          return new ai_three_way_merget(
            std::move(hf), std::move(df), std::move(st));
        }
      }
    }
  }
  else if(options.get_bool_option("legacy-ait"))
  {
    if(options.get_bool_option("constants"))
    {
      // constant_propagator_ait derives from ait<constant_propagator_domaint>
      return new constant_propagator_ait(goto_model.goto_functions);
    }
    else if(options.get_bool_option("dependence-graph"))
    {
      return new dependence_grapht(ns);
    }
    else if(options.get_bool_option("dependence-graph-vs"))
    {
      return new variable_sensitivity_dependence_grapht(
        goto_model.goto_functions, ns, vs_object_factory, vsd_config);
    }
    else if(options.get_bool_option("vsd"))
    {
      auto df = util_make_unique<variable_sensitivity_domain_factoryt>(
        vs_object_factory, vsd_config);
      return new ait<variable_sensitivity_domaint>(std::move(df));
    }
    else if(options.get_bool_option("intervals"))
    {
      return new ait<interval_domaint>();
    }
#if 0
    // Not actually implemented, despite the option...
    else if(options.get_bool_option("non-null"))
    {
      return new ait<non_null_domaint>();
    }
#endif
  }
  else if(options.get_bool_option("legacy-concurrent"))
  {
#if 0
    // Very few domains can work with this interpreter
    // as it requires that changes to the domain are
    // 'non-revertable' and it has merge shared
    if(options.get_bool_option("dependence-graph"))
    {
      return new dependence_grapht(ns);
    }
#endif
  }

  // Construction failed due to configuration errors
  return nullptr;
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

  // Preserve backwards compatibility in processing
  options.set_option("partial-inline", true);
  options.set_option("rewrite-union", false);

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
      analyzer.reset(build_analyzer(options, ns));
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

  add_malloc_may_fail_variable_initializations(goto_model);

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
    " --vsd-values                 value tracking - constants|intervals|set-of-constants\n"
    " --vsd-structs                struct field sensitive analysis - top-bottom|every-field\n"
    " --vsd-arrays                 array entry sensitive analysis - top-bottom|every-element\n"
    " --vsd-pointers               pointer sensitive analysis - top-bottom|constants|value-set\n"
    " --vsd-unions                 union sensitive analysis - top-bottom\n"
    " --vsd-flow-insensitive       disables flow sensitivity\n"
    " --vsd-data-dependencies      track data dependencies\n"
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

void vsd_options(optionst &options, const cmdlinet &cmdline)
{
  options.set_option("domain set", true);

  // Configuration of VSD
  options.set_option("values", cmdline.get_value("vsd-values"));
  options.set_option("pointers", cmdline.get_value("vsd-pointers"));
  options.set_option("arrays", cmdline.get_value("vsd-arrays"));
  options.set_option("structs", cmdline.get_value("vsd-structs"));
  options.set_option("unions", cmdline.get_value("vsd-unions"));
  options.set_option("flow-insensitive", cmdline.isset("vsd-flow-insensitive"));
}
