/*******************************************************************\

Module: Specify write set in code contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#include "assigns.h"

#include <goto-instrument/havoc_utils.h>

#include <langapi/language_util.h>

#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>

#include "utils.h"

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

assigns_clauset::assigns_clauset(
  const exprt::operandst &assigns,
  const messaget &log,
  const namespacet &ns)
  : log(log), ns(ns)
{
  for(const auto &target_expr : assigns)
  {
    add_to_write_set(target_expr);
  }
}

void assigns_clauset::add_to_write_set(const exprt &target_expr)
{
  auto insertion_succeeded = write_set.emplace(*this, target_expr).second;

  if(!insertion_succeeded)
  {
    log.warning() << "Ignored duplicate expression '"
                  << from_expr(ns, target_expr.id(), target_expr)
                  << "' in assigns clause at "
                  << target_expr.source_location().as_string() << messaget::eom;
  }
}

void assigns_clauset::remove_from_write_set(const exprt &target_expr)
{
  write_set.erase(targett(*this, target_expr));
}

exprt assigns_clauset::targett::generate_containment_check(
  const address_of_exprt &lhs_address) const
{
  const auto address_validity = and_exprt{
    all_dereferences_are_valid(dereference_exprt{address}, parent.ns),
    all_dereferences_are_valid(dereference_exprt{lhs_address}, parent.ns)};

  exprt::operandst containment_check;
  containment_check.push_back(same_object(lhs_address, address));

  // If assigns target was a dereference, comparing objects is enough
  // and the resulting condition will be:
  // VALID(self) && VALID(lhs) ==> __CPROVER_same_object(lhs, self)
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
    // (sizeof(self) + __CPROVER_offset(self))
    containment_check.push_back(
      binary_relation_exprt(lhs_region, ID_le, own_region));
  }

  // VALID(self) && VALID(lhs)
  // ==> __CPROVER_same_object(lhs, self)
  //  && __CPROVER_offset(lhs) >= __CPROVER_offset(self)
  //  && (sizeof(lhs) + __CPROVER_offset(lhs)) <=
  //        (sizeof(self) + __CPROVER_offset(self))
  return or_exprt{not_exprt{address_validity}, conjunction(containment_check)};
}

goto_programt
assigns_clauset::generate_havoc_code(const source_locationt &location) const
{
  modifiest modifies;
  for(const auto &target : write_set)
    modifies.insert(target.address.object());

  goto_programt havoc_statements;
  havoc_if_validt havoc_gen(modifies, ns);
  havoc_gen.append_full_havoc_code(location, havoc_statements);

  return havoc_statements;
}

exprt assigns_clauset::generate_containment_check(const exprt &lhs) const
{
  // If write set is empty, no assignment is allowed.
  if(write_set.empty())
    return false_exprt();

  const auto lhs_address = address_of_exprt(targett::normalize(lhs));

  exprt::operandst condition;
  for(const auto &target : write_set)
  {
    condition.push_back(target.generate_containment_check(lhs_address));
  }
  return disjunction(condition);
}
