/*******************************************************************\

Module: Sentinel Doubly Linked Lists

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Axioms

#include "sentinel_dll.h"

#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>

#include "state.h"

optionalt<exprt> sentinel_dll_member(
  const exprt &state,
  const exprt &node,
  bool next, // vs. prev
  const namespacet &ns)
{
  if(node.type().id() != ID_pointer)
    return {};

  if(to_pointer_type(node.type()).base_type().id() != ID_struct_tag)
    return {};

  const auto &struct_type =
    ns.follow_tag(to_struct_tag_type(to_pointer_type(node.type()).base_type()));

  // the first pointer to a struct is 'next', the second 'prev'
  const struct_typet::componentt *next_m = nullptr, *prev_m = nullptr;

  for(auto &m : struct_type.components())
  {
    if(m.type() == node.type()) // we are strict on the type
    {
      if(next_m == nullptr)
        next_m = &m;
      else
        prev_m = &m;
    }
  }

  struct_typet::componentt component;

  if(next)
  {
    if(next_m == nullptr)
      return {};
    else
      component = *next_m;
  }
  else
  {
    if(prev_m == nullptr)
      return {};
    else
      component = *prev_m;
  }

  auto field_address = field_address_exprt(
    node, component.get_name(), pointer_type(component.type()));

  return evaluate_exprt(state, field_address, component.type());
}

optionalt<exprt>
sentinel_dll_next(const exprt &state, const exprt &node, const namespacet &ns)
{
  return sentinel_dll_member(state, node, true, ns);
}

optionalt<exprt>
sentinel_dll_prev(const exprt &state, const exprt &node, const namespacet &ns)
{
  return sentinel_dll_member(state, node, false, ns);
}
