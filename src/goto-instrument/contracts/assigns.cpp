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
  exprt::operandst address_validity;
  exprt::operandst containment_check;

  // __CPROVER_w_ok(target, sizeof(target))
  address_validity.push_back(w_ok_exprt(
    address,
    size_of_expr(dereference_exprt(address).type(), parent.ns).value()));

  // __CPROVER_w_ok(lhs, sizeof(lhs))
  address_validity.push_back(w_ok_exprt(
    lhs_address,
    size_of_expr(dereference_exprt(lhs_address).type(), parent.ns).value()));

  // __CPROVER_same_object(lhs, target)
  containment_check.push_back(same_object(lhs_address, address));

  // If assigns target was a dereference, comparing objects is enough
  // and the resulting condition will be
  // __CPROVER_w_ok(target, sizeof(target))
  // && __CPROVER_w_ok(lhs, sizeof(lhs))
  // ==> __CPROVER_same_object(lhs, target)
  if(id != ID_dereference)
  {
    const auto lhs_offset = pointer_offset(lhs_address);
    const auto own_offset = pointer_offset(address);

    // __CPROVER_offset(lhs) >= __CPROVER_offset(target)
    containment_check.push_back(
      binary_relation_exprt(lhs_offset, ID_ge, own_offset));

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
    containment_check.push_back(
      binary_relation_exprt(lhs_region, ID_le, own_region));
  }

  // __CPROVER_w_ok(target, sizeof(target))
  // && __CPROVER_w_ok(lhs, sizeof(lhs))
  // ==> __CPROVER_same_object(lhs, target)
  //     && __CPROVER_offset(lhs) >= __CPROVER_offset(target)
  //     && (sizeof(lhs) + __CPROVER_offset(lhs)) <=
  //        (sizeof(target) + __CPROVER_offset(target))
  return binary_relation_exprt(
    conjunction(address_validity), ID_implies, conjunction(containment_check));
}

assigns_clauset::assigns_clauset(
  const exprt &expr,
  const messaget &log,
  const namespacet &ns)
  : location(expr.source_location()), log(log), ns(ns)
{
  for(const auto &target_expr : expr.operands())
  {
    add_to_global_write_set(target_expr);
  }
}

void assigns_clauset::add_to_global_write_set(const exprt &target_expr)
{
  auto insertion_succeeded =
    global_write_set.emplace(*this, target_expr).second;

  if(!insertion_succeeded)
  {
    log.warning() << "Ignored duplicate expression '"
                  << from_expr(ns, target_expr.id(), target_expr)
                  << "' in assigns clause at "
                  << target_expr.source_location().as_string() << messaget::eom;
  }
}

void assigns_clauset::remove_from_global_write_set(const exprt &target_expr)
{
  global_write_set.erase(targett(*this, target_expr));
}

void assigns_clauset::add_to_local_write_set(const exprt &expr)
{
  local_write_set.emplace(*this, expr);
}

void assigns_clauset::remove_from_local_write_set(const exprt &expr)
{
  local_write_set.erase(targett(*this, expr));
}

goto_programt assigns_clauset::generate_havoc_code() const
{
  modifiest modifies;
  for(const auto &target : global_write_set)
    modifies.insert(target.address.object());

  for(const auto &target : local_write_set)
    modifies.insert(target.address.object());

  goto_programt havoc_statements;
  append_havoc_code(location, modifies, havoc_statements);
  return havoc_statements;
}

exprt assigns_clauset::generate_containment_check(const exprt &lhs) const
{
  // If write set is empty, no assignment is allowed.
  if(global_write_set.empty() && local_write_set.empty())
    return false_exprt();

  const auto lhs_address = address_of_exprt(targett::normalize(lhs));

  exprt::operandst condition;
  for(const auto &target : local_write_set)
  {
    condition.push_back(target.generate_containment_check(lhs_address));
  }
  for(const auto &target : global_write_set)
  {
    condition.push_back(target.generate_containment_check(lhs_address));
  }
  return disjunction(condition);
}

exprt assigns_clauset::generate_subset_check(
  const assigns_clauset &subassigns) const
{
  if(subassigns.global_write_set.empty())
    return true_exprt();

  INVARIANT(
    subassigns.local_write_set.empty(),
    "Local write set for function calls should be empty at this point.\n" +
      subassigns.location.as_string());

  exprt result = true_exprt();
  for(const auto &subtarget : subassigns.global_write_set)
  {
    exprt::operandst current_subtarget_found_conditions;
    for(const auto &target : global_write_set)
    {
      current_subtarget_found_conditions.push_back(
        target.generate_containment_check(subtarget.address));
    }
    for(const auto &target : local_write_set)
    {
      current_subtarget_found_conditions.push_back(
        target.generate_containment_check(subtarget.address));
    }
    result = and_exprt(result, disjunction(current_subtarget_found_conditions));
  }

  return result;
}
