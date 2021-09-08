/*******************************************************************\

Module: Specify write set in code contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#include "assigns.h"

#include <goto-instrument/havoc_utils.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_predicates.h>

assigns_clauset::targett::targett(
  const assigns_clauset &parent,
  const exprt &expr)
  : expr(address_of_exprt(expr)), id(expr.id()), parent(parent)
{
}

exprt assigns_clauset::targett::normalize(const exprt &expr)
{
  if(expr.id() != ID_address_of)
    return expr;

  const auto &object = to_address_of_expr(expr).object();
  if(object.id() != ID_index)
    return object;

  return to_index_expr(object).array();
}

exprt assigns_clauset::targett::generate_alias_check(const exprt &lhs) const
{
  exprt::operandst condition;
  const auto lhs_ptr =
    (lhs.id() == ID_address_of) ? lhs : address_of_exprt(lhs);

  // __CPROVER_w_ok(target, sizeof(target))
  condition.push_back(w_ok_exprt(
    expr, size_of_expr(dereference_exprt(expr).type(), parent.ns).value()));

  // __CPROVER_same_object(lhs, target)
  condition.push_back(same_object(lhs_ptr, expr));

  // If assigns target was a dereference, comparing objects is enough
  if(id == ID_dereference)
  {
    return conjunction(condition);
  }

  const auto lhs_offset = pointer_offset(lhs_ptr);
  const auto own_offset = pointer_offset(expr);

  // __CPROVER_offset(lhs) >= __CPROVER_offset(target)
  condition.push_back(binary_relation_exprt(lhs_offset, ID_ge, own_offset));

  const auto lhs_region = plus_exprt(
    typecast_exprt::conditional_cast(
      size_of_expr(lhs.type(), parent.ns).value(), lhs_offset.type()),
    lhs_offset);

  const exprt own_region = plus_exprt(
    typecast_exprt::conditional_cast(
      size_of_expr(dereference_exprt(expr).type(), parent.ns).value(),
      own_offset.type()),
    own_offset);

  // (sizeof(lhs) + __CPROVER_offset(lhs)) <=
  // (sizeof(target) + __CPROVER_offset(target))
  condition.push_back(binary_relation_exprt(lhs_region, ID_le, own_region));

  return conjunction(condition);
}

exprt assigns_clauset::targett::generate_compatibility_check(
  const assigns_clauset::targett &other_target) const
{
  return same_object(other_target.expr, expr);
}

assigns_clauset::assigns_clauset(
  const exprt &expr,
  const messaget &log,
  const namespacet &ns)
  : expr(expr), log(log), ns(ns)
{
  for(const auto &target_expr : expr.operands())
  {
    add_target(target_expr);
  }
}

void assigns_clauset::add_target(const exprt &target_expr)
{
  auto insertion_succeeded =
    targets.emplace(*this, targett::normalize(target_expr)).second;

  if(!insertion_succeeded)
  {
    log.warning() << "Ignored duplicate expression '"
                  << from_expr(ns, target_expr.id(), target_expr)
                  << "' in assigns clause at "
                  << target_expr.source_location().as_string() << messaget::eom;
  }
}

goto_programt assigns_clauset::generate_havoc_code() const
{
  modifiest modifies;
  for(const auto &target : targets)
    modifies.insert(to_address_of_expr(target.expr).object());

  goto_programt havoc_statements;
  append_havoc_code(expr.source_location(), modifies, havoc_statements);
  return havoc_statements;
}

exprt assigns_clauset::generate_alias_check(const exprt &lhs) const
{
  // If write set is empty, no assignment is allowed.
  if(targets.empty())
  {
    return false_exprt();
  }

  exprt::operandst condition;
  for(const auto &target : targets)
  {
    condition.push_back(target.generate_alias_check(lhs));
  }
  return disjunction(condition);
}

exprt assigns_clauset::generate_compatibility_check(
  const assigns_clauset &called_assigns) const
{
  if(called_assigns.targets.empty())
  {
    return true_exprt();
  }

  bool first_clause = true;
  exprt result = true_exprt();
  for(const auto &called_target : called_assigns.targets)
  {
    bool first_iter = true;
    exprt current_target_compatible = false_exprt();
    for(const auto &target : targets)
    {
      if(first_iter)
      {
        // TODO: Optimize the validation below and remove code duplication
        // See GitHub issue #6105 for further details

        // Validating the called target through __CPROVER_w_ok() is
        // only useful when the called target is a dereference
        const auto &called_target_ptr = called_target.expr;
        if(
          to_address_of_expr(called_target_ptr).object().id() == ID_dereference)
        {
          // or_exprt is short-circuited, therefore
          // target.generate_compatibility_check(*called_target) would not be
          // checked on invalid called_targets.
          current_target_compatible = or_exprt(
            not_exprt(w_ok_exprt(
              called_target_ptr, from_integer(0, unsigned_int_type()))),
            target.generate_compatibility_check(called_target));
        }
        else
        {
          current_target_compatible =
            target.generate_compatibility_check(called_target);
        }
        first_iter = false;
      }
      else
      {
        current_target_compatible = or_exprt(
          current_target_compatible,
          target.generate_compatibility_check(called_target));
      }
    }
    if(first_clause)
    {
      result = current_target_compatible;
      first_clause = false;
    }
    else
    {
      result = and_exprt(result, current_target_compatible);
    }
  }

  return result;
}
