/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_lift_memory_predicates.h"

#include <util/cprover_prefix.h>
#include <util/format_expr.h>
#include <util/graph.h>
#include <util/pointer_expr.h>
#include <util/replace_symbol.h>
#include <util/symbol.h>

#include <goto-programs/goto_model.h>

#include "dfcc_instrument.h"
#include "dfcc_library.h"
#include "dfcc_utils.h"

dfcc_lift_memory_predicatest::dfcc_lift_memory_predicatest(
  goto_modelt &goto_model,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument,
  message_handlert &message_handler)
  : goto_model(goto_model),
    utils(utils),
    library(library),
    instrument(instrument),
    log(message_handler)
{
}

/// True if a function had at least one of its parameters lifted
bool dfcc_lift_memory_predicatest::is_lifted_function(
  const irep_idt &function_id)
{
  return lifted_parameters.find(function_id) != lifted_parameters.end();
}

/// True iff function_id is a core memory predicate
static bool is_core_memory_predicate(const irep_idt &function_id)
{
  return (function_id == CPROVER_PREFIX "is_fresh") ||
         (function_id == CPROVER_PREFIX "pointer_in_range_dfcc") ||
         (function_id == CPROVER_PREFIX "obeys_contract");
}

bool dfcc_lift_memory_predicatest::calls_memory_predicates(
  const goto_programt &goto_program,
  const std::set<irep_idt> &predicates)
{
  for(const auto &instruction : goto_program.instructions)
  {
    if(
      instruction.is_function_call() &&
      instruction.call_function().id() == ID_symbol)
    {
      const auto &callee_id =
        to_symbol_expr(instruction.call_function()).get_identifier();

      if(
        is_core_memory_predicate(callee_id) ||
        predicates.find(callee_id) != predicates.end())
      {
        return true;
      }
    }
  }
  return false;
}

std::set<irep_idt> dfcc_lift_memory_predicatest::lift_predicates(
  std::set<irep_idt> &discovered_function_pointer_contracts)
{
  std::set<irep_idt> candidates;
  for(const auto &pair : goto_model.symbol_table)
  {
    if(
      pair.second.type.id() == ID_code &&
      !instrument.do_not_instrument(pair.first))
    {
      const auto &iter =
        goto_model.goto_functions.function_map.find(pair.first);
      if(
        iter != goto_model.goto_functions.function_map.end() &&
        iter->second.body_available())
      {
        candidates.insert(pair.first);
      }
    }
  }

  std::set<irep_idt> predicates;

  // iterate until no new predicate is found
  bool new_predicates_found = true;
  while(new_predicates_found)
  {
    new_predicates_found = false;
    for(const auto &function_id : candidates)
    {
      if(
        predicates.find(function_id) == predicates.end() &&
        calls_memory_predicates(
          goto_model.goto_functions.function_map[function_id].body, predicates))
      {
        predicates.insert(function_id);
        new_predicates_found = true;
      }
    }
  }

  if(predicates.empty())
    return predicates;

  // some predicates were found, build dependency graph
  struct dep_graph_nodet : public graph_nodet<empty_edget>
  {
    const irep_idt &function_id;
    explicit dep_graph_nodet(const irep_idt &function_id)
      : function_id(function_id)
    {
    }
  };

  grapht<dep_graph_nodet> dep_graph;

  // inverse mapping from names to dep_graph_nodet identifiers
  std::map<irep_idt, std::size_t> id_to_node_map;
  // create all nodes
  for(auto &predicate : predicates)
  {
    id_to_node_map.insert({predicate, dep_graph.add_node(predicate)});
  }

  // create all edges
  for(auto &caller : predicates)
  {
    const auto caller_id = id_to_node_map[caller];
    for(const auto &instruction :
        goto_model.goto_functions.function_map[caller].body.instructions)
    {
      if(
        instruction.is_function_call() &&
        instruction.call_function().id() == ID_symbol)
      {
        const auto &callee =
          to_symbol_expr(instruction.call_function()).get_identifier();
        if(predicates.find(callee) != predicates.end())
        {
          log.conditional_output(log.debug(), [&](messaget::mstreamt &mstream) {
            mstream << "Memory predicate dependency " << caller << " -> "
                    << callee << messaget::eom;
          });
          const auto callee_id = id_to_node_map[callee];
          if(callee != caller) // do not add edges for self-recursive functions
            dep_graph.add_edge(callee_id, caller_id);
        }
      }
    }
  }

  // lift in dependency order
  auto sorted = dep_graph.topsort();
  PRECONDITION_WITH_DIAGNOSTICS(
    !sorted.empty(),
    "could not determine instrumentation order for memory predicates, most "
    "likely due to mutual recursion");
  for(const auto &idx : sorted)
  {
    lift_predicate(
      dep_graph[idx].function_id, discovered_function_pointer_contracts);
  }

  return predicates;
}

// returns an optional rank
static optionalt<std::size_t> is_param_expr(
  const exprt &expr,
  const std::map<irep_idt, std::size_t> &parameter_rank)
{
  if(expr.id() == ID_typecast)
  {
    // ignore typecasts
    return is_param_expr(to_typecast_expr(expr).op(), parameter_rank);
  }
  else if(expr.id() == ID_symbol)
  {
    const irep_idt &ident = to_symbol_expr(expr).get_identifier();
    const auto found = parameter_rank.find(ident);
    if(found != parameter_rank.end())
    {
      return {found->second};
    }
    else
    {
      return {};
    }
  }
  else
  {
    // bail on anything else
    return {};
  }
}

void dfcc_lift_memory_predicatest::collect_parameters_to_lift(
  const irep_idt &function_id)
{
  const symbolt &function_symbol = utils.get_function_symbol(function_id);
  // map of parameter name to its rank in the signature
  std::map<irep_idt, std::size_t> parameter_rank;
  const auto &parameters = to_code_type(function_symbol.type).parameters();
  for(std::size_t rank = 0; rank < parameters.size(); rank++)
  {
    parameter_rank[parameters[rank].get_identifier()] = rank;
  }
  const goto_programt &body =
    goto_model.goto_functions.function_map[function_id].body;
  for(const auto &it : body.instructions)
  {
    // for all function calls, if a parameter of function_id is passed
    // in a lifted position, add its rank to the set of lifted parameters
    if(it.is_function_call() && it.call_function().id() == ID_symbol)
    {
      const irep_idt &callee_id =
        to_symbol_expr(it.call_function()).get_identifier();
      if(callee_id == CPROVER_PREFIX "is_fresh")
      {
        auto opt_rank = is_param_expr(it.call_arguments()[0], parameter_rank);
        if(opt_rank.has_value())
        {
          lifted_parameters[function_id].insert(opt_rank.value());
        }
      }
      else if(callee_id == CPROVER_PREFIX "pointer_in_range_dfcc")
      {
        auto opt_rank = is_param_expr(it.call_arguments()[1], parameter_rank);
        if(opt_rank.has_value())
        {
          lifted_parameters[function_id].insert(opt_rank.value());
        }
      }
      else if(callee_id == CPROVER_PREFIX "obeys_contract")
      {
        auto opt_rank = is_param_expr(it.call_arguments()[0], parameter_rank);
        if(opt_rank.has_value())
        {
          lifted_parameters[function_id].insert(opt_rank.value());
        }
      }
      else if(is_lifted_function(callee_id))
      {
        // search wether a parameter of function_id is passed to a lifted
        // parameter of callee_id
        for(const std::size_t callee_rank : lifted_parameters[callee_id])
        {
          auto opt_rank =
            is_param_expr(it.call_arguments()[callee_rank], parameter_rank);
          if(opt_rank.has_value())
          {
            lifted_parameters[function_id].insert(opt_rank.value());
          }
        }
      }
    }
  }
}

void dfcc_lift_memory_predicatest::add_pointer_type(
  const irep_idt &function_id,
  const std::size_t parameter_rank,
  replace_symbolt &replace_lifted_param)
{
  symbolt &function_symbol = utils.get_function_symbol(function_id);
  code_typet &code_type = to_code_type(function_symbol.type);
  auto &parameters = code_type.parameters();
  auto &parameter_id = parameters[parameter_rank].get_identifier();
  auto entry = goto_model.symbol_table.symbols.find(parameter_id);
  log.conditional_output(log.debug(), [&](messaget::mstreamt &mstream) {
    mstream << "adding pointer type to " << function_id << " " << parameter_id
            << messaget::eom;
  });
  const symbolt &old_symbol = entry->second;
  const auto &old_symbol_expr = old_symbol.symbol_expr();
  // create new parameter symbol, same everything except type
  symbolt new_symbol(
    old_symbol.name, pointer_type(old_symbol.type), old_symbol.mode);
  new_symbol.base_name = old_symbol.base_name;
  new_symbol.location = old_symbol.location;
  new_symbol.module = old_symbol.module;
  new_symbol.is_lvalue = old_symbol.is_lvalue;
  new_symbol.is_state_var = old_symbol.is_state_var;
  new_symbol.is_thread_local = old_symbol.is_thread_local;
  new_symbol.is_file_local = old_symbol.is_file_local;
  new_symbol.is_auxiliary = old_symbol.is_auxiliary;
  new_symbol.is_parameter = old_symbol.is_parameter;
  goto_model.symbol_table.erase(entry);
  std::pair<symbolt &, bool> res =
    goto_model.symbol_table.insert(std::move(new_symbol));
  CHECK_RETURN(res.second);
  replace_lifted_param.insert(
    old_symbol_expr, dereference_exprt(res.first.symbol_expr()));
  code_typet::parametert parameter(res.first.type);
  parameter.set_base_name(res.first.base_name);
  parameter.set_identifier(res.first.name);
  parameters[parameter_rank] = parameter;
}

void dfcc_lift_memory_predicatest::lift_parameters_and_update_body(
  const irep_idt &function_id,
  std::set<irep_idt> &discovered_function_pointer_contracts)
{
  replace_symbolt replace_lifted_params;
  // add pointer types to all parameters that require it
  for(const auto rank : lifted_parameters[function_id])
  {
    add_pointer_type(function_id, rank, replace_lifted_params);
  }
  auto &body = goto_model.goto_functions.function_map[function_id].body;
  // update the function body
  for(auto &instruction : body.instructions)
  {
    // rewrite all occurrences of lifted parameters
    instruction.transform([&replace_lifted_params](exprt expr) {
      const bool changed = !replace_lifted_params.replace(expr);
      return changed ? optionalt<exprt>{expr} : nullopt;
    });

    // add address-of to all arguments expressions passed in lifted position to
    // another memory predicate
    if(
      instruction.is_function_call() &&
      instruction.call_function().id() == ID_symbol)
    {
      // add address-of to arguments that are passed in lifted position
      auto &callee_id =
        to_symbol_expr(instruction.call_function()).get_identifier();
      if(is_lifted_function(callee_id))
      {
        for(const auto &rank : lifted_parameters[callee_id])
        {
          const auto arg = instruction.call_arguments()[rank];
          log.conditional_output(log.debug(), [&](messaget::mstreamt &mstream) {
            mstream << "Adding address_of to call " << callee_id
                    << ", argument " << format(arg) << messaget::eom;
          });
          instruction.call_arguments()[rank] = address_of_exprt(arg);
        }
      }
    }
  }
}

void dfcc_lift_memory_predicatest::lift_predicate(
  const irep_idt &function_id,
  std::set<irep_idt> &discovered_function_pointer_contracts)
{
  // when this function_id gets processed, any memory predicate it calls has
  // already been processed (except itself if it is recursive);

  log.status() << "Instrumenting memory predicate '" << function_id << "'"
               << messaget::eom;

  // first step: identify which parameters are passed directly to core
  // predicates of lifted positions in user-defined memory predicates and mark
  // them as lifted
  collect_parameters_to_lift(function_id);
  lift_parameters_and_update_body(
    function_id, discovered_function_pointer_contracts);

  log.conditional_output(log.debug(), [&](messaget::mstreamt &mstream) {
    mstream << "Ranks of lifted parameters for " << function_id << ": ";
    for(const auto rank : lifted_parameters[function_id])
      mstream << rank << ", ";
    mstream << messaget::eom;
  });

  // instrument the function for side effects: adds the write_set parameter,
  // adds checks for side effects, maps core predicates to their implementation.
  instrument.instrument_function(
    function_id, discovered_function_pointer_contracts);
}

void dfcc_lift_memory_predicatest::fix_calls(goto_programt &program)
{
  fix_calls(program, program.instructions.begin(), program.instructions.end());
}

void dfcc_lift_memory_predicatest::fix_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction)
{
  for(auto target = first_instruction; target != last_instruction; target++)
  {
    if(target->is_function_call())
    {
      const auto &function = target->call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &fun_name = to_symbol_expr(function).get_identifier();

        if(is_lifted_function(fun_name))
        {
          // add address-of on all lifted argumnents
          for(const auto rank : lifted_parameters[fun_name])
          {
            target->call_arguments()[rank] =
              address_of_exprt(target->call_arguments()[rank]);
          }
        }
      }
    }
  }
}
