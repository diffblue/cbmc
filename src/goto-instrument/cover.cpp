/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

/// \file
/// Coverage Instrumentation

#include "cover.h"

#include <util/config.h>
#include <util/message.h>
#include <util/make_unique.h>
#include <util/cmdline.h>
#include <util/options.h>
#include <util/deprecate.h>

#include <goto-programs/remove_skip.h>

#include "cover_basic_blocks.h"

/// Applies instrumenters to given goto program
/// \param goto_program: the goto program
/// \param instrumenters: the instrumenters
/// \param mode: mode of the function to instrument (for instance ID_C or
///   ID_java)
/// \param message_handler: a message handler
void instrument_cover_goals(
  goto_programt &goto_program,
  const cover_instrumenterst &instrumenters,
  const irep_idt &mode,
  message_handlert &message_handler)
{
  const std::unique_ptr<cover_blocks_baset> basic_blocks =
    mode == ID_java ? std::unique_ptr<cover_blocks_baset>(
                        new cover_basic_blocks_javat(goto_program))
                    : std::unique_ptr<cover_blocks_baset>(
                        new cover_basic_blockst(goto_program));

  basic_blocks->report_block_anomalies(goto_program, message_handler);
  instrumenters(goto_program, *basic_blocks);
}

/// Instruments goto program for a given coverage criterion
/// \param symbol_table: the symbol table
/// \param goto_program: the goto program
/// \param criterion: the coverage criterion
/// \param message_handler: a message handler
/// \deprecated use instrument_cover_goals(goto_programt &goto_program,
/// const cover_instrumenterst &instrumenters,
/// message_handlert &message_handler, const irep_idt mode) instead
DEPRECATED("use instrument_cover_goals(goto_programt &...) instead")
void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont criterion,
  message_handlert &message_handler)
{
  goal_filterst goal_filters;
  goal_filters.add(util_make_unique<internal_goals_filtert>(message_handler));

  cover_instrumenterst instrumenters;
  instrumenters.add_from_criterion(criterion, symbol_table, goal_filters);

  instrument_cover_goals(
    goto_program, instrumenters, ID_unknown, message_handler);
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
  else
  {
    std::stringstream s;
    s << "unknown coverage criterion " << '\'' << criterion_string << '\'';
    throw s.str();
  }

  return c;
}

/// Parses coverage-related  command line options
/// \param cmdline: the command line
/// \param options: the options
void parse_cover_options(const cmdlinet &cmdline, optionst &options)
{
  options.set_option("cover", cmdline.get_values("cover"));
  std::string cover_include_pattern =
    cmdline.get_value("cover-include-pattern");
  if(cmdline.isset("cover-function-only"))
  {
    std::regex special_characters(
      "\\.|\\\\|\\*|\\+|\\?|\\{|\\}|\\[|\\]|\\(|\\)|\\^|\\$|\\|");
    cover_include_pattern =
      ".*" + std::regex_replace(config.main, special_characters, "\\$&") + ".*";
  }
  options.set_option("cover-include-pattern", cover_include_pattern);
  options.set_option("no-trivial-tests", cmdline.isset("no-trivial-tests"));
  options.set_option(
    "cover-traces-must-terminate",
    cmdline.isset("cover-traces-must-terminate"));
}

/// Build data structures controlling coverage from command-line options.
/// \param options: command-line options
/// \param symbol_table: global symbol table
/// \param message_handler: used to log incorrect option specifications
/// \return a cover_configt on success, or null otherwise.
std::unique_ptr<cover_configt> get_cover_config(
  const optionst &options,
  const symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  std::unique_ptr<cover_configt> config = util_make_unique<cover_configt>();
  function_filterst &function_filters = config->function_filters;
  goal_filterst &goal_filters = config->goal_filters;
  cover_instrumenterst &instrumenters = config->cover_instrumenters;

  function_filters.add(
    util_make_unique<internal_functions_filtert>(message_handler));

  goal_filters.add(util_make_unique<internal_goals_filtert>(message_handler));

  optionst::value_listt criteria_strings = options.get_list_option("cover");

  config->keep_assertions = false;
  for(const auto &criterion_string : criteria_strings)
  {
    try
    {
      coverage_criteriont c = parse_coverage_criterion(criterion_string);

      if(c == coverage_criteriont::ASSERTION)
        config->keep_assertions = true;

      instrumenters.add_from_criterion(c, symbol_table, goal_filters);
    }
    catch(const std::string &e)
    {
      msg.error() << e << messaget::eom;
      return {};
    }
  }

  if(config->keep_assertions && criteria_strings.size()>1)
  {
    msg.error() << "assertion coverage cannot currently be used together with "
                << "other coverage criteria" << messaget::eom;
    return {};
  }

  // cover entry point function only
  std::string cover_include_pattern =
    options.get_option("cover-include-pattern");
  if(!cover_include_pattern.empty())
  {
    function_filters.add(
      util_make_unique<include_pattern_filtert>(
        message_handler, cover_include_pattern));
  }

  if(options.get_bool_option("no-trivial-tests"))
    function_filters.add(
      util_make_unique<trivial_functions_filtert>(message_handler));

  config->traces_must_terminate =
    options.get_bool_option("cover-traces-must-terminate");

  return config;
}

/// Instruments a single goto program based on the given configuration
/// \param config: configuration, produced using get_cover_config
/// \param function_id: function name
/// \param function: function function to instrument
/// \param message_handler: log output
static void instrument_cover_goals(
  const cover_configt &config,
  const irep_idt &function_id,
  goto_functionst::goto_functiont &function,
  message_handlert &message_handler)
{
  if(!config.keep_assertions)
  {
    Forall_goto_program_instructions(i_it, function.body)
    {
      // Simplify the common case where we have ASSERT(x); ASSUME(x):
      if(i_it->is_assert())
      {
        auto successor = std::next(i_it);
        if(successor != function.body.instructions.end() &&
           successor->is_assume() &&
           successor->guard == i_it->guard)
        {
          successor->make_skip();
        }
        i_it->type = goto_program_instruction_typet::ASSUME;
      }
    }
  }

  bool changed = false;

  if(config.function_filters(function_id, function))
  {
    instrument_cover_goals(
      function.body, config.cover_instrumenters, config.mode, message_handler);
    changed = true;
  }

  if(config.traces_must_terminate &&
     function_id == goto_functionst::entry_point())
  {
    cover_instrument_end_of_function(function_id, function.body);
    changed = true;
  }

  if(changed)
    remove_skip(function.body);
}

/// Instruments a single goto program based on the given configuration
/// \param config: configuration, produced using get_cover_config
/// \param function: goto program to instrument
/// \param message_handler: log output
void instrument_cover_goals(
  const cover_configt &config,
  goto_model_functiont &function,
  message_handlert &message_handler)
{
  instrument_cover_goals(
    config,
    function.get_function_id(),
    function.get_goto_function(),
    message_handler);

  function.compute_location_numbers();
}

/// Instruments goto functions based on given command line options
/// \param options: the options
/// \param symbol_table: the symbol table
/// \param goto_functions: the goto functions
/// \param message_handler: a message handler
bool instrument_cover_goals(
  const optionst &options,
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  msg.status() << "Rewriting existing assertions as assumptions"
               << messaget::eom;

  std::unique_ptr<cover_configt> config =
    get_cover_config(options, symbol_table, message_handler);
  if(!config)
    return true;

  if(config->traces_must_terminate &&
     !goto_functions.function_map.count(goto_functions.entry_point()))
  {
    msg.error() << "cover-traces-must-terminate: invalid entry point ["
                << goto_functions.entry_point() << "]" << messaget::eom;
    return true;
  }

  Forall_goto_functions(f_it, goto_functions)
  {
    config->mode = symbol_table.lookup(f_it->first)->mode;
    instrument_cover_goals(
      *config, f_it->first, f_it->second, message_handler);
  }
  goto_functions.compute_location_numbers();

  config->function_filters.report_anomalies();
  config->goal_filters.report_anomalies();

  return false;
}

/// Instruments a goto model based on given command line options
/// \param options: the options
/// \param goto_model: the goto model
/// \param message_handler: a message handler
bool instrument_cover_goals(
  const optionst &options,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  return instrument_cover_goals(
    options,
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
}
