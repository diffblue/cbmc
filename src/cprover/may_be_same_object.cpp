/*******************************************************************\

Module: May Be Same Object

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// May Be Same Object

#include "may_be_same_object.h"

#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>

#include "may_alias.h"

exprt strip_member_element(const exprt &src)
{
  if(src.id() == ID_element_address)
    return strip_member_element(to_element_address_expr(src).base());
  else if(src.id() == ID_field_address)
    return strip_member_element(to_field_address_expr(src).base());
  else
    return src;
}

exprt may_be_same_object(
  const exprt &a,
  const exprt &b,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  auto a_stripped = strip_member_element(a);
  auto b_stripped = strip_member_element(b);

  if(a_stripped == b_stripped)
    return true_exprt();
  else if(
    a_stripped.id() == ID_object_address &&
    b_stripped.id() == ID_object_address)
    return false_exprt();

  if(stack_and_not_dirty(a, address_taken, ns))
    return false_exprt();

  if(stack_and_not_dirty(b, address_taken, ns))
    return false_exprt();

  return ::same_object(a_stripped, b_stripped);
}
