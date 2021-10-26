/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

/// \file
/// Coverage Instrumentation

#include "cover.h"

#include <util/message.h>
#include <util/make_unique.h>
#include <util/cmdline.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include "cover_basic_blocks.h"

/// Applies instrumenters to given goto program
/// \param function_id: name of \p goto_program
/// \param goto_program: the goto program
/// \param instrumenters: the instrumenters
/// \param mode: mode of the function to instrument (for instance ID_C or
///   ID_java)
/// \param message_handler: a message handler
/// \param make_assertion: A function which takes an expression, with a source
///   location and makes an assertion based on that expression. The expression
///   asserted is expected to include the expression passed in, but may include
///   other additional conditions.
static void instrument_cover_goals(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const cover_instrumenterst &instrumenters,
  const irep_idt &mode,
  message_handlert &message_handler,
  const cover_instrumenter_baset::assertion_factoryt &make_assertion)
{
  const std::unique_ptr<cover_blocks_baset> basic_blocks =
    mode == ID_java ? std::unique_ptr<cover_blocks_baset>(
                        new cover_basic_blocks_javat(goto_program))
                    : std::unique_ptr<cover_blocks_baset>(
                        new cover_basic_blockst(goto_program));

  basic_blocks->report_block_anomalies(
    function_id, goto_program, message_handler);
  instrumenters(function_id, goto_program, *basic_blocks, make_assertion);
}

/// Create and add an instrumenter based on the given criterion
/// \param criterion: the coverage criterion
/// \param symbol_table: the symbol table
/// \param goal_filters: goal filters to discard certain goals
void cover_instrumenterst::add_from_criterion(
  coverage_criteriont criterion,
  const symbol_tablet &symbol_table,
  const goal_filterst &goal_filters)
{
  switch(criterion)
  {
  case coverage_criteriont::LOCATION:
    instrumenters.push_back(
      util_make_unique<cover_location_instrumentert>(
        symbol_table, goal_filters));
    break;
  case coverage_criteriont::BRANCH:
    instrumenters.push_back(
      util_make_unique<cover_branch_instrumentert>(symbol_table, goal_filters));
    break;
  case coverage_criteriont::DECISION:
    instrumenters.push_back(
      util_make_unique<cover_decision_instrumentert>(
        symbol_table, goal_filters));
    break;
  case coverage_criteriont::CONDITION:
    instrumenters.push_back(
      util_make_unique<cover_condition_instrumentert>(
        symbol_table, goal_filters));
    break;
  case coverage_criteriont::PATH:
    instrumenters.push_back(
      util_make_unique<cover_path_instrumentert>(symbol_table, goal_filters));
    break;
  case coverage_criteriont::MCDC:
    instrumenters.push_back(
      util_make_unique<cover_mcdc_instrumentert>(symbol_table, goal_filters));
    break;
  case coverage_criteriont::ASSERTION:
    instrumenters.push_back(
      util_make_unique<cover_assertion_instrumentert>(
        symbol_table, goal_filters));
    break;
  case coverage_criteriont::COVER:
    instrumenters.push_back(
      util_make_unique<cover_cover_instrumentert>(symbol_table, goal_filters));
    break;
  case coverage_criteriont::ASSUME:
    instrumenters.push_back(
      util_make_unique<cover_assume_instrumentert>(symbol_table, goal_filters));
  }
}

/// Parses a coverage criterion
/// \param criterion_string: a string
/// \return a coverage criterion or throws an exception
coverage_criteriont
parse_coverage_criterion(const std::string &criterion_string)
{
  coverage_criteriont c;

  if(criterion_string == "assertion" || criterion_string == "assertions")
    c = coverage_criteriont::ASSERTION;
  else if(criterion_string == "path" || criterion_string == "paths")
    c = coverage_criteriont::PATH;
  else if(criterion_string == "branch" || criterion_string == "branches")
    c = coverage_criteriont::BRANCH;
  else if(criterion_string == "location" || criterion_string == "locations")
    c = coverage_criteriont::LOCATION;
  else if(criterion_string == "decision" || criterion_string == "decisions")
    c = coverage_criteriont::DECISION;
  else if(criterion_string == "condition" || criterion_string == "conditions")
    c = coverage_criteriont::CONDITION;
  else if(criterion_string == "mcdc")
    c = coverage_criteriont::MCDC;
  else if(criterion_string == "cover")
    c = coverage_criteriont::COVER;
  else if(criterion_string == "assume")
    c = coverage_criteriont::ASSUME;
  else
  {
    std::stringstream s;
    s << "unknown coverage criterion " << '\'' << criterion_string << '\'';
    throw invalid_command_line_argument_exceptiont(s.str(), "--cover");
  }

  return c;
}

/// Parses coverage-related  command line options
/// \param cmdline: the command line
/// \param options: the options
void parse_cover_options(const cmdlinet &cmdline, optionst &options)
{
  options.set_option("cover", cmdline.get_values("cover"));

  // allow retrieving full traces
  options.set_option("simple-slice", false);

  options.set_option(
    "cover-include-pattern", cmdline.get_value("cover-include-pattern"));
  options.set_option("no-trivial-tests", cmdline.isset("no-trivial-tests"));

  std::string cover_only = cmdline.get_value("cover-only");

  if(!cover_only.empty() && cmdline.isset("cover-function-only"))
    throw invalid_command_line_argument_exceptiont(
      "at most one of --cover-only and --cover-function-only can be used",
      "--cover-only");

  options.set_option("cover-only", cmdline.get_value("cover-only"));
  if(cmdline.isset("cover-function-only"))
    options.set_option("cover-only", "function");

  options.set_option(
    "cover-traces-must-terminate",
    cmdline.isset("cover-traces-must-terminate"));
  options.set_option(
    "cover-failed-assertions", cmdline.isset("cover-failed-assertions"));

  options.set_option("show-test-suite", cmdline.isset("show-test-suite"));
}

/// Build data structures controlling coverage from command-line options.
/// Do not include the options that depend on the main function specified by the
/// user.
/// \param options: command-line options
/// \param symbol_table: global symbol table
/// \param message_handler: used to log incorrect option specifications
/// \return a cover_configt on success, or null otherwise.
cover_configt get_cover_config(
  const optionst &options,
  const symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  cover_configt cover_config;
  function_filterst &function_filters =
    cover_config.cover_configt::function_filters;
  std::unique_ptr<goal_filterst> &goal_filters = cover_config.goal_filters;
  cover_instrumenterst &instrumenters = cover_config.cover_instrumenters;

  function_filters.add(util_make_unique<internal_functions_filtert>());

  goal_filters->add(util_make_unique<internal_goals_filtert>());

  optionst::value_listt criteria_strings = options.get_list_option("cover");

  cover_config.keep_assertions = false;
  for(const auto &criterion_string : criteria_strings)
  {
    coverage_criteriont c = parse_coverage_criterion(criterion_string);

    if(c == coverage_criteriont::ASSERTION)
      cover_config.keep_assertions = true;
    // Make sure that existing assertions don't get replaced by assumes
    else if(c == coverage_criteriont::ASSUME)
      cover_config.keep_assertions = true;

    instrumenters.add_from_criterion(c, symbol_table, *goal_filters);
  }

  if(cover_config.keep_assertions && criteria_strings.size() > 1)
  {
    std::stringstream s;
    s << "assertion coverage cannot currently be used together with other"
      << "coverage criteria";
    throw invalid_command_line_argument_exceptiont(s.str(), "--cover");
  }

  std::string cover_include_pattern =
    options.get_option("cover-include-pattern");
  if(!cover_include_pattern.empty())
  {
    function_filters.add(
      util_make_unique<include_pattern_filtert>(cover_include_pattern));
  }

  if(options.get_bool_option("no-trivial-tests"))
    function_filters.add(util_make_unique<trivial_functions_filtert>());

  cover_config.traces_must_terminate =
    options.get_bool_option("cover-traces-must-terminate");

  cover_config.cover_failed_assertions =
    options.get_bool_option("cover-failed-assertions");

  return cover_config;
}

/// Build data structures controlling coverage from command-line options.
/// Include options that depend on the main function specified by the user.
/// \param options: command-line options
/// \param main_function_id: symbol of the user-specified main program function
/// \param symbol_table: global symbol table
/// \param message_handler: used to log incorrect option specifications
/// \return a cover_configt on success, or null otherwise.
cover_configt get_cover_config(
  const optionst &options,
  const irep_idt &main_function_id,
  const symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  cover_configt cover_config =
    get_cover_config(options, symbol_table, message_handler);

  std::string cover_only = options.get_option("cover-only");

  // cover entry point function only
  if(cover_only == "function")
  {
    const symbolt &main_symbol = symbol_table.lookup_ref(main_function_id);
    cover_config.function_filters.add(
      util_make_unique<single_function_filtert>(main_symbol.name));
  }
  else if(cover_only == "file")
  {
    const symbolt &main_symbol = symbol_table.lookup_ref(main_function_id);
    cover_config.function_filters.add(
      util_make_unique<file_filtert>(main_symbol.location.get_file()));
  }
  else if(!cover_only.empty())
  {
    std::stringstream s;
    s << "Argument to --cover-only not recognized: " << cover_only;
    throw invalid_command_line_argument_exceptiont(s.str(), "--cover-only");
  }

  return cover_config;
}

/// Instruments a single goto program based on the given configuration
/// \param cover_config: configuration, produced using get_cover_config
/// \param function_symbol: symbol of the function to be instrumented
/// \param function: function to instrument
/// \param message_handler: log output
static void instrument_cover_goals(
  const cover_configt &cover_config,
  const symbolt &function_symbol,
  goto_functionst::goto_functiont &function,
  message_handlert &message_handler)
{
  if(!cover_config.keep_assertions)
  {
    Forall_goto_program_instructions(i_it, function.body)
    {
      // Simplify the common case where we have ASSERT(x); ASSUME(x):
      if(i_it->is_assert())
      {
        if(!cover_config.cover_failed_assertions)
        {
          auto successor = std::next(i_it);
          if(
            successor != function.body.instructions.end() &&
            successor->is_assume() &&
            successor->get_condition() == i_it->get_condition())
          {
            successor->turn_into_skip();
          }

          i_it->turn_into_assume();
        }
        else
        {
          i_it->turn_into_skip();
        }
      }
    }
  }

  bool changed = false;

  if(cover_config.function_filters(function_symbol, function))
  {
    messaget msg(message_handler);
    msg.debug() << "Instrumenting coverage for function "
                << id2string(function_symbol.name) << messaget::eom;
    instrument_cover_goals(
      function_symbol.name,
      function.body,
      cover_config.cover_instrumenters,
      function_symbol.mode,
      message_handler,
      cover_config.make_assertion);
    changed = true;
  }

  if(
    cover_config.traces_must_terminate &&
    function_symbol.name == goto_functionst::entry_point())
  {
    cover_instrument_end_of_function(
      function_symbol.name, function.body, cover_config.make_assertion);
    changed = true;
  }

  if(changed)
    remove_skip(function.body);
}

/// Instruments a single goto program based on the given configuration
/// \param cover_config: configuration, produced using get_cover_config
/// \param function: goto program to instrument
/// \param message_handler: log output
void instrument_cover_goals(
  const cover_configt &cover_config,
  goto_model_functiont &function,
  message_handlert &message_handler)
{
  const symbolt function_symbol =
    function.get_symbol_table().lookup_ref(function.get_function_id());
  instrument_cover_goals(
    cover_config,
    function_symbol,
    function.get_goto_function(),
    message_handler);

  function.compute_location_numbers();
}

/// Instruments goto functions based on given command line options
/// \param cover_config: configuration, produced using get_cover_config
/// \param symbol_table: the symbol table
/// \param goto_functions: the goto functions
/// \param message_handler: a message handler
bool instrument_cover_goals(
  const cover_configt &cover_config,
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  msg.status() << "Rewriting existing assertions as assumptions"
               << messaget::eom;

  if(
    cover_config.traces_must_terminate &&
    !goto_functions.function_map.count(goto_functions.entry_point()))
  {
    msg.error() << "cover-traces-must-terminate: invalid entry point ["
                << goto_functions.entry_point() << "]" << messaget::eom;
    return true;
  }

  for(auto &gf_entry : goto_functions.function_map)
  {
    const symbolt function_symbol = symbol_table.lookup_ref(gf_entry.first);
    instrument_cover_goals(
      cover_config, function_symbol, gf_entry.second, message_handler);
  }
  goto_functions.compute_location_numbers();

  cover_config.function_filters.report_anomalies();
  cover_config.goal_filters->report_anomalies();

  return false;
}

/// Instruments a goto model based on given command line options
/// \param cover_config: configuration, produced using get_cover_config
/// \param goto_model: the goto model
/// \param message_handler: a message handler
bool instrument_cover_goals(
  const cover_configt &cover_config,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  return instrument_cover_goals(
    cover_config,
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
}
