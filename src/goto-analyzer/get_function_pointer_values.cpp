/*******************************************************************\

Module: Show function pointer values

Author: Diffblue Ltd, 2020

\*******************************************************************/

#include "get_function_pointer_values.h"

#include <util/message.h>
#include <util/namespace.h>
#include <util/optional.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/restrict_function_pointers.h>

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

#include <regex>
#include <string>

namespace
{
struct get_function_pointer_values_common_argst
{
  const ai_baset &ai;
  const namespacet ns;
};

/// assuming the exprt passed in is an address-of-function, get
/// the name of that function
irep_idt get_function_pointer_name(const exprt &function_pointer)
{
  return to_symbol_expr(to_address_of_expr(function_pointer).op())
    .get_identifier();
}

/// Get the names of function pointers of a value set of function pointers.
/// This returns an empty set if the value set is empty, and nullopt if the
/// value set was top (i.e. we can't extract a finite set of restrictions
/// just looking at the value set).
optionalt<std::unordered_set<irep_idt>>
get_function_names_from_function_pointer_value_set(
  const value_set_abstract_objectt *value_set)
{
  std::unordered_set<irep_idt> result;
  // TODO: This is currently dealing with the slightly odd situation that
  // a value set abstract object actually contains more abstract objects.
  // Going forward we'll have to change this.
  for(const auto &elem : value_set->get_values())
  {
    if(elem->is_top())
    {
      return nullopt;
    }
    else if(elem->is_bottom())
    {
      return std::unordered_set<irep_idt>{};
    }
    else
    {
      result.insert(get_function_pointer_name(elem->to_constant()));
    }
  }
  return result;
}

optionalt<std::unordered_set<irep_idt>>
evaluate_function_pointer_value_set_after_assignment(
  const get_function_pointer_values_common_argst &args,
  const symbol_exprt &restriction_symbol,
  const ai_baset::locationt &instruction_location)
{
  // don't inline this, this needs to stay in scope as long as we access
  // the casted state
  auto const state_after_assignment_unique_ptr =
    args.ai.abstract_state_after(instruction_location);

  CHECK_RETURN(state_after_assignment_unique_ptr != nullptr);

  auto const state_after_assignment =
    dynamic_cast<const variable_sensitivity_domaint *>(
      state_after_assignment_unique_ptr.get());

  INVARIANT(
    state_after_assignment != nullptr,
    "the context calling this is responsible for making sure the abstract"
    " interpretation happens in the variable sensitivity domain");

  auto const restriction_abstract_object =
    state_after_assignment->eval(restriction_symbol, args.ns);

  CHECK_RETURN(restriction_abstract_object != nullptr);

  auto const restriction_value_set_abstract_object =
    dynamic_cast<const value_set_abstract_objectt *>(
      restriction_abstract_object.get());

  INVARIANT(
    restriction_value_set_abstract_object != nullptr,
    "the context calling this is responsible for making sure"
    " function pointers evaluate to value sets");

  return get_function_names_from_function_pointer_value_set(
    restriction_value_set_abstract_object);
}

bool is_assignment_to_function_pointer_callsite(
  const goto_programt::const_targett &location)
{
  static auto const callsite_identifier_regex =
    std::regex{R"(\w+\.function_pointer_call\.\d+)"};
  if(!location->is_assign())
  {
    // only interested in assignment
    return false;
  }
  auto const assignment = location->get_assign();
  if(!can_cast_expr<symbol_exprt>(assignment.lhs()))
  {
    // only interested in assignments to symbol
    return false;
  }
  auto const lhs_identifier =
    id2string(to_symbol_expr(assignment.lhs()).get_identifier());
  return std::regex_match(lhs_identifier, callsite_identifier_regex);
}

void get_function_pointer_values_handle_function(
  const get_function_pointer_values_common_argst &args,
  function_pointer_restrictionst::restrictionst &restrictions,
  const goto_functiont &goto_function)
{
  for_each_instruction_if(
    goto_function,
    is_assignment_to_function_pointer_callsite,
    [&](const goto_programt::const_targett &location) {
      auto const callsite_symbol = to_symbol_expr(location->get_assign().lhs());
      if(
        auto callsite_restrictions =
          evaluate_function_pointer_value_set_after_assignment(
            args, callsite_symbol, location))
      {
        restrictions.insert({callsite_symbol.get_identifier(),
                             std::move(*callsite_restrictions)});
      }
    });
}

} // namespace

function_pointer_restrictionst
get_function_pointer_restrictions_from_value_set_ai(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  message_handlert &message_handler)
{
  auto args = get_function_pointer_values_common_argst{
    ai, namespacet{goto_model.get_symbol_table()}};
  auto restrictions = function_pointer_restrictionst::restrictionst{};
  auto message = messaget{message_handler};
  message.status() << "Getting function pointer targets at specific callsites"
                   << messaget::eom;

  for(auto const &function_entry : goto_model.goto_functions.function_map)
  {
    get_function_pointer_values_handle_function(
      args, restrictions, function_entry.second);
  }
  return function_pointer_restrictionst{std::move(restrictions)};
}
