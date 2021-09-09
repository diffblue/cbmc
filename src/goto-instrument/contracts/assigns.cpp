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
  : address(address_of_exprt(normalize(expr))),
    expr(expr),
    id(expr.id()),
    parent(parent)
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

exprt assigns_clauset::targett::generate_containment_check(
  const address_of_exprt &lhs_address) const
{
  exprt::operandst condition;

  // __CPROVER_w_ok(target, sizeof(target))
  condition.push_back(w_ok_exprt(
    address,
    size_of_expr(dereference_exprt(address).type(), parent.ns).value()));

  // __CPROVER_same_object(lhs, target)
  condition.push_back(same_object(lhs_address, address));

  // If assigns target was a dereference, comparing objects is enough
  if(id == ID_dereference)
  {
    return conjunction(condition);
  }

  const auto lhs_offset = pointer_offset(lhs_address);
  const auto own_offset = pointer_offset(address);

  // __CPROVER_offset(lhs) >= __CPROVER_offset(target)
  condition.push_back(binary_relation_exprt(lhs_offset, ID_ge, own_offset));

  const auto lhs_region = plus_exprt(
    typecast_exprt::conditional_cast(
      size_of_expr(lhs_address.object().type(), parent.ns).value(),
      lhs_offset.type()),
    lhs_offset);

  const exprt own_region = plus_exprt(
    typecast_exprt::conditional_cast(
      size_of_expr(address.object().type(), parent.ns).value(),
      own_offset.type()),
    own_offset);

  // (sizeof(lhs) + __CPROVER_offset(lhs)) <=
  // (sizeof(target) + __CPROVER_offset(target))
  condition.push_back(binary_relation_exprt(lhs_region, ID_le, own_region));

  return conjunction(condition);
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
  auto insertion_succeeded = targets.emplace(*this, target_expr).second;

  if(!insertion_succeeded)
  {
    log.warning() << "Ignored duplicate expression '"
                  << from_expr(ns, target_expr.id(), target_expr)
                  << "' in assigns clause at "
                  << target_expr.source_location().as_string() << messaget::eom;
  }
}

void assigns_clauset::remove_target(const exprt &target_expr)
{
  targets.erase(targett(*this, targett::normalize(target_expr)));
}

goto_programt assigns_clauset::generate_havoc_code() const
{
  modifiest modifies;
  for(const auto &target : targets)
    modifies.insert(target.address.object());

  goto_programt havoc_statements;
  append_havoc_code(expr.source_location(), modifies, havoc_statements);
  return havoc_statements;
}

exprt assigns_clauset::generate_containment_check(const exprt &lhs) const
{
  // If write set is empty, no assignment is allowed.
  if(targets.empty())
    return false_exprt();

  const auto lhs_address = address_of_exprt(targett::normalize(lhs));

  exprt::operandst condition;
  for(const auto &target : targets)
  {
    condition.push_back(target.generate_containment_check(lhs_address));
  }
  return disjunction(condition);
}

exprt assigns_clauset::generate_subset_check(
  const assigns_clauset &subassigns) const
{
  if(subassigns.targets.empty())
    return true_exprt();

  exprt result = true_exprt();
  for(const auto &subtarget : subassigns.targets)
  {
    // TODO: Optimize the implication generated due to the validity check.
    // In some cases, e.g. when `subtarget` is known to be `NULL`,
    // the implication can be skipped entirely. See #6105 for more details.
    auto validity_check =
      w_ok_exprt(subtarget.address, from_integer(0, unsigned_int_type()));

    exprt::operandst current_subtarget_found_conditions;
    for(const auto &target : targets)
    {
      current_subtarget_found_conditions.push_back(
        target.generate_containment_check(subtarget.address));
    }

    auto current_subtarget_found = or_exprt(
      not_exprt(validity_check),
      disjunction(current_subtarget_found_conditions));

    result = and_exprt(result, current_subtarget_found);
  }

  return result;
}
