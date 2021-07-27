/*******************************************************************\

Module: Specify write set in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#include "assigns.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_predicates.h>

assigns_clause_targett::assigns_clause_targett(
  const exprt &object_ptr,
  code_contractst &contract,
  messaget &log_parameter,
  const irep_idt &function_id)
  : pointer_object(pointer_for(object_ptr)),
    contract(contract),
    init_block(),
    log(log_parameter),
    local_target(typet())
{
  INVARIANT(
    pointer_object.type().id() == ID_pointer,
    "Assigns clause targets should be stored as pointer expressions.");

  const symbolt &function_symbol = contract.ns.lookup(function_id);

  // Declare a new symbol to stand in for the reference
  symbolt standin_symbol = contract.new_tmp_symbol(
    pointer_object.type(),
    function_symbol.location,
    function_symbol.mode);

  local_target = standin_symbol.symbol_expr();

  // Build standin variable initialization block
  init_block.add(
    goto_programt::make_decl(local_target, function_symbol.location));
  init_block.add(goto_programt::make_assignment(
    code_assignt(local_target, pointer_object), function_symbol.location));
}

assigns_clause_targett::~assigns_clause_targett()
{
}

std::vector<symbol_exprt> assigns_clause_targett::temporary_declarations() const
{
  std::vector<symbol_exprt> result;
  result.push_back(local_target);
  return result;
}

exprt assigns_clause_targett::alias_expression(const exprt &ptr)
{
  return same_object(ptr, local_target);
}

exprt assigns_clause_targett::compatible_expression(
  const assigns_clause_targett &called_target)
{
  return alias_expression(called_target.get_direct_pointer());
}

goto_programt
assigns_clause_targett::havoc_code(source_locationt location) const
{
  goto_programt assigns_havoc;

  exprt lhs = dereference_exprt(pointer_object);
  side_effect_expr_nondett rhs(lhs.type(), location);

  goto_programt::targett target =
    assigns_havoc.add(goto_programt::make_assignment(
      code_assignt(std::move(lhs), std::move(rhs)), location));
  target->code_nonconst().add_source_location() = location;

  return assigns_havoc;
}

const exprt &assigns_clause_targett::get_direct_pointer() const
{
  return pointer_object;
}

goto_programt &assigns_clause_targett::get_init_block()
{
  return init_block;
}

assigns_clauset::assigns_clauset(
  const exprt &assigns,
  code_contractst &contract,
  const irep_idt function_id,
  messaget log_parameter)
  : assigns_expr(assigns),
    parent(contract),
    function_id(function_id),
    log(log_parameter)
{
  for(exprt current_operation : assigns_expr.operands())
  {
    add_target(current_operation);
  }
}

assigns_clauset::~assigns_clauset()
{
  for(assigns_clause_targett *target : targets)
  {
    delete target;
  }
}

assigns_clause_targett *assigns_clauset::add_target(exprt current_operation)
{
  assigns_clause_targett *target = new assigns_clause_targett(
    (current_operation.id() == ID_address_of)
      ? to_index_expr(to_address_of_expr(current_operation).object()).array()
      : current_operation,
    parent,
    log,
    function_id);
  targets.push_back(target);
  return target;
}

assigns_clause_targett *
assigns_clauset::add_pointer_target(exprt current_operation)
{
  return add_target(dereference_exprt(current_operation));
}

goto_programt assigns_clauset::init_block(source_locationt location)
{
  goto_programt result;
  for(assigns_clause_targett *target : targets)
  {
    for(goto_programt::instructiont inst :
        target->get_init_block().instructions)
    {
      result.add(goto_programt::instructiont(inst));
    }
  }
  return result;
}

goto_programt &assigns_clauset::temporary_declarations(
  source_locationt location,
  irep_idt function_name,
  irep_idt language_mode)
{
  if(standin_declarations.empty())
  {
    for(assigns_clause_targett *target : targets)
    {
      for(symbol_exprt symbol : target->temporary_declarations())
      {
        standin_declarations.add(
          goto_programt::make_decl(symbol, symbol.source_location()));
      }
    }
  }
  return standin_declarations;
}

goto_programt assigns_clauset::dead_stmts(
  source_locationt location,
  irep_idt function_name,
  irep_idt language_mode)
{
  goto_programt dead_statements;
  for(assigns_clause_targett *target : targets)
  {
    for(symbol_exprt symbol : target->temporary_declarations())
    {
      dead_statements.add(
        goto_programt::make_dead(symbol, symbol.source_location()));
    }
  }
  return dead_statements;
}

goto_programt assigns_clauset::havoc_code(
  source_locationt location,
  irep_idt function_name,
  irep_idt language_mode)
{
  goto_programt havoc_statements;
  for(assigns_clause_targett *target : targets)
  {
    // (1) If the assigned target is not a dereference,
    // only include the havoc_statement

    // (2) If the assigned target is a dereference, do the following:

    // if(!__CPROVER_w_ok(target, 0)) goto z;
    //      havoc_statements
    // z: skip

    // create the z label
    goto_programt tmp_z;
    goto_programt::targett z = tmp_z.add(goto_programt::make_skip(location));

    const auto &target_ptr = target->get_direct_pointer();

    if(to_address_of_expr(target_ptr).object().id() == ID_dereference)
    {
      // create the condition
      exprt condition =
        not_exprt(w_ok_exprt(target_ptr, from_integer(0, unsigned_int_type())));
      havoc_statements.add(goto_programt::make_goto(z, condition, location));
    }

    // create havoc_statements
    for(goto_programt::instructiont instruction :
        target->havoc_code(location).instructions)
    {
      havoc_statements.add(std::move(instruction));
    }

    if(to_address_of_expr(target_ptr).object().id() == ID_dereference)
    {
      // add the z label instruction
      havoc_statements.destructive_append(tmp_z);
    }
  }
  return havoc_statements;
}

exprt assigns_clauset::alias_expression(const exprt &lhs)
{
  if(targets.empty())
  {
    return false_exprt();
  }

  exprt left_ptr = assigns_clause_targett::pointer_for(lhs);

  bool first_iter = true;
  exprt result = false_exprt();
  for(assigns_clause_targett *target : targets)
  {
    if(first_iter)
    {
      result = target->alias_expression(left_ptr);
      first_iter = false;
    }
    else
    {
      result = or_exprt(result, target->alias_expression(left_ptr));
    }
  }
  return result;
}

exprt assigns_clauset::compatible_expression(
  const assigns_clauset &called_assigns)
{
  if(called_assigns.targets.empty())
  {
    return true_exprt();
  }

  bool first_clause = true;
  exprt result = true_exprt();
  for(assigns_clause_targett *called_target : called_assigns.targets)
  {
    bool first_iter = true;
    exprt current_target_compatible = false_exprt();
    for(assigns_clause_targett *target : targets)
    {
      if(first_iter)
      {
        // TODO: Optimize the validation below and remove code duplication
        // See GitHub issue #6105 for further details

        // Validating the called target through __CPROVER_w_ok() is
        // only useful when the called target is a dereference
        const auto &called_target_ptr = called_target->get_direct_pointer();
        if(
          to_address_of_expr(called_target_ptr).object().id() == ID_dereference)
        {
          // or_exprt is short-circuited, therefore
          // target->compatible_expression(*called_target) would not be
          // checked on invalid called_targets.
          current_target_compatible = or_exprt(
            not_exprt(w_ok_exprt(
              called_target_ptr, from_integer(0, unsigned_int_type()))),
            target->compatible_expression(*called_target));
        }
        else
        {
          current_target_compatible =
            target->compatible_expression(*called_target);
        }
        first_iter = false;
      }
      else
      {
        current_target_compatible = or_exprt(
          current_target_compatible,
          target->compatible_expression(*called_target));
      }
    }
    if(first_clause)
    {
      result = current_target_compatible;
      first_clause = false;
    }
    else
    {
      exprt::operandst conjuncts;
      conjuncts.push_back(result);
      conjuncts.push_back(current_target_compatible);
      result = conjunction(conjuncts);
    }
  }

  return result;
}
