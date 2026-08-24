/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include "static_instrument.h"

#include <util/c_types.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/message.h>
#include <util/options.h>
#include <util/prefix.h>
#include <util/string_utils.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/system_library_symbols.h>
#include <goto-programs/write_goto_binary.h>

#include <analyses/ai.h>

#include <map>

static std::string s_function_start = "function_start";
static std::string s_function_end = "function_end";
static std::string s_function_call = "function_call";
static std::string s_function_return = "function_return";
static std::string s_any_goto_target = "any_goto_target";
static std::string s_backwards_goto_target = "backwards_goto_target";
static std::string s_after_goto_not_taken = "after_goto_not_taken";

// Build a configuration from user strings
instrument_configt::instrument_configt(const std::string &opts)
{
  // Initialise everything to the defaults
  function_start = instrument_actiont::NOTHING;
  function_end = instrument_actiont::NOTHING;
  function_call = instrument_actiont::NOTHING;
  function_return = instrument_actiont::NOTHING;
  any_goto_target = instrument_actiont::NOTHING;
  backwards_goto_target = instrument_actiont::NOTHING;
  after_goto_not_taken = instrument_actiont::NOTHING;
  requires = false;
  ensures = false;

  if(opts == "")
  {
    return;
  }

  // A helper struct
  struct config_targett
  {
    const std::string &name;
    instrument_actiont *target;

    config_targett(const std::string &n, instrument_actiont *t)
      : name(n), target(t)
    {
    }
  };

  std::vector<config_targett> options;
  options.push_back(config_targett(s_function_start, &(this->function_start)));
  options.push_back(config_targett(s_function_end, &(this->function_end)));
  options.push_back(config_targett(s_function_call, &(this->function_call)));
  options.push_back(
    config_targett(s_function_return, &(this->function_return)));
  options.push_back(
    config_targett(s_any_goto_target, &(this->any_goto_target)));
  options.push_back(
    config_targett(s_backwards_goto_target, &(this->backwards_goto_target)));
  options.push_back(
    config_targett(s_after_goto_not_taken, &(this->after_goto_not_taken)));

  auto const config_strings = split_string(opts, ',');
  for(auto const &config_string : config_strings)
  {
    instrument_actiont *target = NULL;
    std::string remainder = "";

    for(auto const &option : options)
    {
      if(config_string.substr(0, option.name.length()) == option.name)
      {
        target = option.target;
        remainder = config_string.substr(option.name.length());
        break;
      }
    }

    if(target == NULL)
    {
      if(config_string == "requires")
      {
        requires = true;
      }
      else if(config_string == "ensures")
      {
        ensures = true;
      }
      else
      {
        throw invalid_command_line_argument_exceptiont(
          "Unrecognised instrument option: " + config_string, opts);
      }
    }
    else
    {
      if((remainder == "") || (remainder == "=assume"))
        *target = instrument_actiont::ASSUME;
      else if(remainder == "=assert")
        *target = instrument_actiont::ASSERT;
      else if(remainder == "=nothing")
        *target = instrument_actiont::NOTHING;
      else
      {
        throw invalid_command_line_argument_exceptiont(
          "Unrecognised instrument action: " + remainder, opts);
      }
    }
  }
}

typedef std::map<
  goto_programt::targett,
  std::pair<instrument_actiont, const std::string *>,
  goto_programt::target_less_than>
  instrument_locationst;

static instrument_locationst get_instrumentation_locations(
  goto_programt &gp,
  const instrument_configt &config)
{
  instrument_locationst targets;

  goto_programt::targett prev_it = gp.instructions.begin();
  Forall_goto_program_instructions(i_it, gp)
  {
    instrument_actiont action = instrument_actiont::NOTHING;
    std::string *reason;

    if(i_it == gp.instructions.begin())
    {
      action = config.function_start;
      reason = &s_function_start;
    }
    else if(i_it->is_end_function())
    {
      action = config.function_end;
      reason = &s_function_end;
    }
    else if(i_it->is_function_call())
    {
      action = config.function_call;
      reason = &s_function_call;
    }
    else if(prev_it->is_function_call())
    {
      action = config.function_return;
      reason = &s_function_return;
    }
    else if(i_it->is_target())
    {
      action = config.any_goto_target;
      reason = &s_any_goto_target;

      // Choices for backwards_goto override any_goto if present
      if(config.backwards_goto_target != instrument_actiont::NOTHING)
      {
        for(auto const incoming_it : i_it->incoming_edges)
        {
          if(incoming_it->is_backwards_goto())
          {
            action = config.backwards_goto_target;
            reason = &s_backwards_goto_target;
            break; // inner!
          }
        }
      }
    }
    else if(prev_it->is_goto() && !prev_it->condition().is_true())
    {
      action = config.after_goto_not_taken;
      reason = &s_after_goto_not_taken;
    }

    if(action != instrument_actiont::NOTHING)
    {
      targets.emplace(i_it, std::make_pair(action, reason));
    }

    // This bit is vital!
    prev_it = i_it;
  }

  return targets;
}

static exprt compute_instrumentation_expression(
  goto_programt::targett i_it,
  const ai_baset &ai,
  const namespacet &ns,
  const std::set<exprt> &relevant_expressions,
  messaget &m)
{
  // Multiple histories are handled as disjunctions
  exprt::operandst inst;

  const auto trace_set_pointer =
    ai.abstract_traces_before(i_it); // Keep a pointer so refcount > 0
  const auto &trace_set = *trace_set_pointer;

  if(trace_set.size() == 0) // i.e. unreachable
  {
    m.progress() << "unreachable... "; // No EOM yet

    inst.push_back(false_exprt{});
  }
  else if(trace_set.size() == 1)
  {
    auto dp = ai.abstract_state_before(i_it);

    m.progress() << "single history... "; // No EOM yet

    inst.push_back(dp->to_predicate(relevant_expressions, ns));
  }
  else
  {
    m.progress() << "multiple histories... "; // No EOM yet

    for(const auto &trace_ptr : trace_set)
    {
      auto dp = ai.abstract_state_before(trace_ptr);
      inst.push_back(dp->to_predicate(relevant_expressions, ns));
    }
  }

  return disjunction(inst);
}

static void
get_globals(std::set<exprt> &relevant_expressions, const namespacet &ns)
{
  system_library_symbolst lib;
  std::set<std::string> out; // Unused

  for(const auto &symbol_pair : ns.get_symbol_table().symbols)
  {
    const symbolt &symbol = symbol_pair.second;
    auto name_string = id2string(symbol.name);
    if(
      symbol.is_lvalue && symbol.is_static_lifetime &&
      !lib.is_symbol_internal_symbol(symbol, out))
    {
      relevant_expressions.insert(symbol_exprt(symbol.name, symbol.type));
    }
  }
  return;
}

static void get_locals(
  std::set<exprt> &relevant_expressions,
  const goto_programt &goto_program,
  const namespacet &ns)
{
  goto_programt::decl_identifierst locals;
  goto_program.get_decl_identifiers(locals);
  for(const auto &identifier : locals)
  {
    const symbolt &symbol = ns.lookup(identifier);
    relevant_expressions.insert(symbol_exprt(identifier, symbol.type));
  }
  return;
}

static void get_arguments(
  std::set<exprt> &relevant_expressions,
  const irep_idt function_name,
  const namespacet &ns)
{
  const symbolt &symbol = ns.lookup(function_name);
  const code_typet &type = to_code_type(symbol.type);

  for(const auto &param : type.parameters())
  {
    relevant_expressions.insert(
      symbol_exprt(param.get_identifier(), param.type()));
  }
  return;
}

static void static_instrument_goto_program(
  const irep_idt function_name,
  goto_programt &goto_program,
  symbol_tablet &symbol_table,
  const namespacet &ns,
  const ai_baset &ai,
  const instrument_configt &config,
  message_handlert &message_handler)
{
  // Get the locations to instrument
  auto targets = get_instrumentation_locations(goto_program, config);

  // The state may contain information about variables from other
  // scopes, such as the caller which are true but putting them into
  // instrumentation can cause problems.  So gather the local
  // variables.
  std::set<exprt> relevant_expressions;
  get_globals(relevant_expressions, ns);
  get_locals(relevant_expressions, goto_program, ns);
  get_arguments(relevant_expressions, function_name, ns);
  // TODO : for pointer variables p, add *p?
  // TODO : rename whatever#return to  __CPROVER_return_value

  // For each of them
  for(const auto &t : targets)
  {
    goto_programt::targett i_it = t.first;
    instrument_actiont action = t.second.first;
    const std::string &reason = *(t.second.second);

    messaget m(message_handler);
    m.status() << "Instruction " << i_it->location_number << " because "
               << reason << "... "; // No EOM

    // Generate the expression
    exprt instrument_expression =
      compute_instrumentation_expression(i_it, ai, ns, relevant_expressions, m);
    m.status() << "condition is " << format(instrument_expression)
               << "... "; // No EOM

    // Insert it!
    goto_programt::targett current = i_it;
    goto_program.insert_before_swap(i_it);

    if(action == instrument_actiont::ASSUME)
    {
      *current = goto_programt::make_assumption(instrument_expression);
      m.progress() << "added as assumption" << messaget::eom;
    }
    else if(action == instrument_actiont::ASSERT)
    {
      *current = goto_programt::make_assertion(instrument_expression);
      m.progress() << "added as assertion" << messaget::eom;
    }
    else
    {
      UNREACHABLE;
    }
    current->source_location_nonconst() = i_it->source_location();
  }

  if(config.requires || config.ensures)
  {
    messaget m(message_handler);

    symbolt *symbol = symbol_table.get_writeable(function_name);
    auto code = to_code_with_contract_type(symbol->type);

    if(config.requires)
    {
      m.status() << "Add requires contract... ";
      exprt instrument_expression = compute_instrumentation_expression(
        goto_program.instructions.begin(), ai, ns, relevant_expressions, m);
      m.status() << "condition is " << format(instrument_expression)
                 << "... "; // No EOM

      code.c_requires().push_back(instrument_expression);
      m.progress() << "added as contract" << messaget::eom;
    }
    if(config.ensures)
    {
      m.status() << "Add ensures contract... ";
      auto i_it = goto_program.instructions.end();
      --i_it;
      exprt instrument_expression = compute_instrumentation_expression(
        i_it, ai, ns, relevant_expressions, m);
      m.status() << "condition is " << format(instrument_expression)
                 << "... "; // No EOM

      code.c_requires().push_back(instrument_expression);
      m.progress() << "added as contract" << messaget::eom;
    }

    // Write back the annotated type
    symbol->type = code;
  }

  goto_program.update(); // Make sure the references are correct.
  return;
}

void static_instrument_goto_model(
  goto_modelt &goto_model,
  const ai_baset &ai,
  const instrument_configt &config,
  message_handlert &message_handler)
{
  messaget m(message_handler);
  m.status() << "Instrumenting goto_model" << messaget::eom;

  const namespacet ns(goto_model.symbol_table);

  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
    {
      m.progress() << "Not instrumenting " << gf_entry.first
                   << " because it has no body" << messaget::eom;
    }
    else
    {
      m.progress() << "Instrumenting " << gf_entry.first << messaget::eom;

      static_instrument_goto_program(
        gf_entry.first,
        gf_entry.second.body,
        goto_model.symbol_table,
        ns,
        ai,
        config,
        message_handler);
    }
  }

  return;
}

/// Uses the domain to_predicate method to generate ASSUMEs or ASSERTs.
/// \param goto_model: the program analyzed
/// \param ai: the abstract interpreter after it has been run to fix point
/// \param options: the parsed user options
/// \param message_handler: the system message handler
/// \param out: output stream for the instrumented program
/// \return false on success with the instrumented program to out
bool static_instrument(
  goto_modelt &goto_model,
  const ai_baset &ai,
  const std::string &configuration_string,
  message_handlert &message_handler,
  std::ostream &out)
{
  instrument_configt config(configuration_string);

  static_instrument_goto_model(goto_model, ai, config, message_handler);

  messaget m(message_handler);
  m.status() << "Writing goto binary" << messaget::eom;

  restore_returns(goto_model); // restore return types before writing the binary
  goto_model.goto_functions.update(); // Make sure the references are correct.

  namespacet ns(goto_model.symbol_table);
  return write_goto_binary(
    out, ns.get_symbol_table(), goto_model.goto_functions);
}
