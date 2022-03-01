/*******************************************************************\

Module: Instrument Contracts

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Instrument Contracts

#include "instrument_contracts.h"

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/replace_symbol.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/expr2c.h>

#include <iostream>

#define MAX_TEXT 20

optionalt<code_with_contract_typet>
get_contract(const irep_idt &function_identifier, const namespacet &ns)
{
  // contracts are in a separate symbol, with prefix "contract::"
  auto contract_identifier = "contract::" + id2string(function_identifier);
  const symbolt *symbol_ptr;
  if(ns.lookup(contract_identifier, symbol_ptr))
    return {}; // symbol not found
  else
    return to_code_with_contract_type(symbol_ptr->type);
}

bool has_contract(const irep_idt &function_identifier, const namespacet &ns)
{
  return get_contract(function_identifier, ns).has_value();
}

static std::string expr2text(const exprt &src, const namespacet &ns)
{
  auto text = expr2c(src, ns);
  if(text.size() >= MAX_TEXT)
    return std::string(text, 0, MAX_TEXT - 3) + "...";
  else
    return text;
}

static exprt make_address(exprt src)
{
  if(src.id() == ID_dereference)
  {
    return to_dereference_expr(src).pointer();
  }
  else
    return address_of_exprt(src);
}

// add the function to the source location
source_locationt
add_function(irep_idt function_identifier, source_locationt src)
{
  if(!src.get_file().empty())
    src.set_function(function_identifier);

  return src;
}

// add the function to the source location
exprt add_function(irep_idt function_identifier, exprt src)
{
  for(auto &op : src.operands())
    op = add_function(function_identifier, op);

  if(!src.source_location().get_file().empty())
    src.add_source_location().set_function(function_identifier);

  return src;
}

exprt replace_source_location(
  exprt src,
  const source_locationt &source_location)
{
  for(auto &op : src.operands())
    op = replace_source_location(op, source_location);

  src.add_source_location() = source_location;

  return src;
}

static bool is_symbol_member(const exprt &expr)
{
  if(expr.id() == ID_symbol)
    return true;
  else if(expr.id() == ID_member)
    return is_symbol_member(to_member_expr(expr).struct_op());
  else
    return false;
}

exprt assigns_match(const exprt &assigns, const exprt &lhs)
{
  if(is_symbol_member(lhs) && assigns == lhs)
    return true_exprt(); // trivial match

  if(lhs.id() == ID_member)
  {
    if(assigns_match(assigns, to_member_expr(lhs).struct_op()).is_true())
      return true_exprt();
  }
  else if(lhs.id() == ID_index)
  {
    if(assigns_match(assigns, to_index_expr(lhs).array()).is_true())
      return true_exprt();
  }

  auto assigns_address = make_address(assigns);
  auto lhs_address = make_address(lhs);

  if(lhs.type() == assigns.type())
  {
    return equal_exprt(assigns_address, lhs_address);
  }
  else
  {
    // need to compare offset ranges
    auto same_object = ::same_object(assigns_address, lhs_address);
    return same_object;
  }
}

static exprt instantiate_contract_lambda(exprt src)
{
  return src.id() == ID_lambda ? to_lambda_expr(src).where() : src;
}

static exprt make_assigns_assertion(
  irep_idt function_identifier,
  const exprt::operandst &assigns,
  const exprt &lhs)
{
  exprt::operandst disjuncts;

  for(auto &assigns_clause : assigns)
  {
    auto a = instantiate_contract_lambda(assigns_clause);

    if(a.id() == ID_conditional_target_group)
    {
      auto &condition = to_binary_expr(a).op0();
      auto &targets = to_multi_ary_expr(to_binary_expr(a).op1());
      for(auto &target : targets.operands())
      {
        auto target_address = make_address(target);
        auto lhs_address = make_address(lhs);
        lhs_address =
          typecast_exprt::conditional_cast(lhs_address, target_address.type());
        disjuncts.push_back(
          and_exprt(condition, equal_exprt(target_address, lhs_address)));
      }
    }
    else
    {
      auto match = assigns_match(a, lhs);

      // trivial?
      if(match.is_true())
        return true_exprt();

      disjuncts.push_back(std::move(match));
    }
  }

  return disjunction(disjuncts);
}

static bool
is_procedure_local(const irep_idt &function_identifier, const exprt &lhs)
{
  if(lhs.id() == ID_member)
    return is_procedure_local(
      function_identifier, to_member_expr(lhs).struct_op());
  else if(lhs.id() == ID_index)
    return is_procedure_local(function_identifier, to_index_expr(lhs).array());
  else if(lhs.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(lhs);
    return has_prefix(
      id2string(symbol_expr.get_identifier()),
      id2string(function_identifier) + "::");
  }
  else
    return false;
}

static bool is_old(const exprt &lhs)
{
  if(lhs.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(lhs);
    return has_prefix(id2string(symbol_expr.get_identifier()), "old::");
  }
  else
    return false;
}

symbol_exprt find_old_expr(
  const exprt &src,
  const std::string &prefix,
  std::vector<std::pair<symbol_exprt, exprt>> &old_exprs)
{
  for(std::size_t i = 0; i < old_exprs.size(); i++)
  {
    if(old_exprs[i].second == src)
      return old_exprs[i].first;
  }

  auto index = old_exprs.size();
  irep_idt identifier = prefix + std::to_string(index);
  old_exprs.emplace_back(symbol_exprt(identifier, src.type()), src);

  return old_exprs.back().first;
}

exprt replace_old(
  exprt src,
  const std::string &prefix,
  std::vector<std::pair<symbol_exprt, exprt>> &old_exprs)
{
  if(src.id() == ID_old)
  {
    const auto &old_expr = to_unary_expr(src);
    return find_old_expr(old_expr.op(), prefix, old_exprs);
  }
  else
  {
    // rec. call
    for(auto &op : src.operands())
      op = replace_old(op, prefix, old_exprs);
    return src;
  }
}

goto_programt old_assignments(
  const std::vector<std::pair<symbol_exprt, exprt>> &old_exprs,
  const source_locationt &source_location)
{
  goto_programt dest;

  for(const auto &old_expr : old_exprs)
  {
    auto lhs = old_expr.first;
    auto fixed_rhs = replace_source_location(old_expr.second, source_location);
    auto assignment_instruction =
      goto_programt::make_assignment(lhs, fixed_rhs, source_location);
    dest.add(std::move(assignment_instruction));
  }

  return dest;
}

void instrument_contract_checks(
  goto_functionst::function_mapt::value_type &f,
  const namespacet &ns)
{
  // contracts are in a separate symbol, with prefix "contract::"
  auto contract_identifier = "contract::" + id2string(f.first);
  const symbolt *symbol_ptr;
  if(ns.lookup(contract_identifier, symbol_ptr))
    return; // nothing to check

  auto &contract = to_code_with_contract_type(symbol_ptr->type);

  auto &body = f.second.body;

  if(body.instructions.empty())
    return; // nothing to check

  // new instructions to add at the beginning of the function
  goto_programt add_at_beginning;

  // precondition?
  if(!contract.requires().empty())
  {
    // stick these in as assumptions, preserving the ordering
    goto_programt dest;
    for(auto &assumption : contract.requires())
    {
      exprt assumption_instance = instantiate_contract_lambda(assumption);
      auto fixed_assumption = add_function(f.first, assumption_instance);
      add_at_beginning.add(goto_programt::make_assumption(
        fixed_assumption, fixed_assumption.source_location()));
    }
  }

  // record "old(...)" expressions.
  std::vector<std::pair<symbol_exprt, exprt>> old_exprs;
  const auto old_prefix = "old::" + id2string(f.first);

  // postcondition?
  if(!contract.ensures().empty())
  {
    // Stick the postconditions in as assertions at the end
    auto last = body.instructions.end();
    if(std::prev(last)->is_end_function())
      last = std::prev(last);

    for(auto &assertion : contract.ensures())
    {
      exprt assertion_instance = instantiate_contract_lambda(assertion);

      std::string comment = "postcondition";
      if(contract.ensures().size() >= 2)
        comment += " " + expr2text(assertion_instance, ns);

      auto location = assertion.source_location();
      location.set_function(f.first); // seems to be missing
      location.set_property_class(ID_postcondition);
      location.set_comment(comment);

      auto replaced_assertion =
        replace_old(assertion_instance, old_prefix, old_exprs);

      auto fixed_assertion = add_function(f.first, replaced_assertion);

      auto assertion_instruction =
        goto_programt::make_assertion(fixed_assertion, std::move(location));

      body.insert_before_swap(last, assertion_instruction);
    }
  }

  // do 'old' in the body
  if(
    !contract.assigns().empty() || !contract.requires().empty() ||
    !contract.ensures().empty())
  {
    for(auto &instruction : body.instructions)
      instruction.transform(
        [&old_prefix, &old_exprs](exprt expr) -> optionalt<exprt> {
          return replace_old(expr, old_prefix, old_exprs);
        });
  }

  // Add assignments to 'old' symbols at the beginning of the function.
  {
    auto tmp =
      old_assignments(old_exprs, add_function(f.first, symbol_ptr->location));
    add_at_beginning.destructive_append(tmp);
  }

  body.destructive_insert(body.instructions.begin(), add_at_beginning);

  // assigns?
  if(
    !contract.assigns().empty() || !contract.requires().empty() ||
    !contract.ensures().empty())
  {
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        it++)
    {
      if(it->is_assign())
      {
        const auto &lhs = it->assign_lhs();

        // Parameter or local or old? Ignore.
        if(is_procedure_local(f.first, lhs))
          continue; // ok

        if(is_old(lhs))
          continue; // ok

        // maybe not ok
        auto assigns_assertion =
          make_assigns_assertion(f.first, contract.assigns(), lhs);
        auto location = it->source_location();
        location.set_property_class("assigns");
        location.set_comment("assigns clause");
        auto assertion_instruction = goto_programt::make_assertion(
          std::move(assigns_assertion), std::move(location));
        body.insert_before_swap(it, assertion_instruction);
        it++; // skip over the assertion we have just generated
      }
    }
  }
}

void replace_function_calls_by_contracts(
  goto_functionst::function_mapt::value_type &f,
  const goto_modelt &goto_model)
{
  auto &body = f.second.body;
  const namespacet ns(goto_model.symbol_table);

  std::size_t call_site_counter = 0;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    if(it->is_function_call())
    {
      const auto &function = it->call_function();
      if(function.id() == ID_symbol)
      {
        const auto &symbol = ns.lookup(to_symbol_expr(function));

        const auto contract_opt = get_contract(symbol.name, ns);

        if(!contract_opt.has_value())
          continue;

        auto &contract = contract_opt.value();

        // record "old(...)" expressions.
        std::vector<std::pair<symbol_exprt, exprt>> old_exprs;
        const auto old_prefix = "old::" + id2string(f.first) + "::call-site-" +
                                std::to_string(++call_site_counter) + "::";

        // need to substitute parameters
        const auto f_it =
          goto_model.goto_functions.function_map.find(symbol.name);

        if(f_it == goto_model.goto_functions.function_map.end())
          DATA_INVARIANT(false, "failed to find function in function_map");

        replace_symbolt replace_symbol;
        const auto &parameters = to_code_type(symbol.type).parameters();
        const auto &arguments = it->call_arguments();

        for(std::size_t p = 0; p < f_it->second.parameter_identifiers.size();
            p++)
        {
          auto p_symbol = symbol_exprt(
            f_it->second.parameter_identifiers[p], parameters[p].type());
          replace_symbol.insert(p_symbol, arguments[p]);
        }

        // replace __CPROVER_return_value by the lhs of the call
        const auto &call_lhs = it->call_lhs();
        replace_symbol.insert(
          symbol_exprt(CPROVER_PREFIX "return_value", call_lhs.type()),
          call_lhs);

        goto_programt dest;

        // assert the preconditions
        for(auto &precondition : contract.requires())
        {
          auto instantiated_precondition =
            instantiate_contract_lambda(precondition);

          auto location = it->source_location();
          location.set_property_class(ID_precondition);
          location.set_comment(
            id2string(symbol.display_name()) + " precondition " +
            expr2text(instantiated_precondition, ns));

          auto replaced_precondition = instantiated_precondition;
          replace_symbol(replaced_precondition);

          dest.add(
            goto_programt::make_assertion(replaced_precondition, location));
        }

        // havoc the 'assigned' variables
        for(auto &assigns_clause_lambda : contract.assigns())
        {
          auto location = it->source_location();

          auto assigns_clause =
            instantiate_contract_lambda(assigns_clause_lambda);

          if(assigns_clause.id() == ID_conditional_target_group)
          {
            const auto &condition = to_binary_expr(assigns_clause).op0();
            auto replaced_condition = condition;
            replace_symbol(replaced_condition);

            const auto &targets =
              to_multi_ary_expr(to_binary_expr(assigns_clause).op1())
                .operands();

            for(auto &target : targets)
            {
              auto rhs = side_effect_expr_nondett(target.type(), location);

              auto replaced_lhs = target;
              replace_symbol(replaced_lhs);

              auto goto_instruction =
                dest.add(goto_programt::make_incomplete_goto(
                  not_exprt(replaced_condition), location));

              dest.add(
                goto_programt::make_assignment(replaced_lhs, rhs, location));

              auto skip_instruction =
                dest.add(goto_programt::make_skip(location));

              goto_instruction->complete_goto(skip_instruction);
            }
          }
          else
          {
            const auto &lhs = assigns_clause;
            auto rhs = side_effect_expr_nondett(lhs.type(), location);

            auto replaced_lhs = lhs;
            replace_symbol(replaced_lhs);
            auto fixed_lhs = replace_source_location(replaced_lhs, location);

            dest.add(goto_programt::make_assignment(fixed_lhs, rhs, location));
          }
        }

        // assume the postconditions
        for(auto &postcondition : contract.ensures())
        {
          auto &location = it->source_location();

          auto replaced_postcondition1 =
            instantiate_contract_lambda(postcondition);
          replace_symbol(replaced_postcondition1);

          auto replaced_postcondition2 =
            replace_old(replaced_postcondition1, old_prefix, old_exprs);

          dest.add(
            goto_programt::make_assumption(replaced_postcondition2, location));
        }

        // now insert the assignents to old::... at the beginning
        // of 'dest'
        {
          auto tmp = old_assignments(old_exprs, it->source_location());
          dest.destructive_insert(dest.instructions.begin(), tmp);
        }

        // remove the function call
        it->turn_into_skip();

        // insert after 'it' to preserve branches to the call
        body.destructive_insert(std::next(it), dest);
      }
    }
  }
}

void instrument_contracts(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto &f : goto_model.goto_functions.function_map)
  {
    instrument_contract_checks(f, ns);
    replace_function_calls_by_contracts(f, goto_model);
  }
}
