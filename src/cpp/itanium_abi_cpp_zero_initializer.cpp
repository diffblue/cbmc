/*******************************************************************\

Module: C++ Language Type Checking

Author: Kiro

\*******************************************************************/

/// \file
/// Zero-initialization and null member pointer values of the Itanium C++ ABI

#include "itanium_abi_cpp_zero_initializer.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/expr_iterator.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <set>

bool is_pointer_to_data_member_type(const typet &type)
{
  return type.id() == ID_pointer && type.find(ID_to_member).is_not_nil() &&
         to_pointer_type(type).base_type().id() != ID_code;
}

exprt null_pointer_to_data_member(const typet &type)
{
  PRECONDITION(is_pointer_to_data_member_type(type));
#ifdef CPROVER_CPP_ITANIUM_DATA_MEMBER_POINTER_NULL
  return typecast_exprt{from_integer(-1, signed_size_type()), type};
#else
  return null_pointer_exprt{to_pointer_type(type)};
#endif
}

static bool contains_pointer_to_data_member(
  const typet &type,
  const namespacet &ns,
  std::set<irep_idt> &visited)
{
  if(is_pointer_to_data_member_type(type))
    return true;
  if(type.id() == ID_array || type.id() == ID_vector)
  {
    return contains_pointer_to_data_member(
      to_type_with_subtype(type).subtype(), ns, visited);
  }
  if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    const irep_idt &identifier = to_tag_type(type).get_identifier();
    if(!visited.insert(identifier).second)
      return false;
    const symbolt *symbol = nullptr;
    if(ns.lookup(identifier, symbol) || symbol == nullptr)
      return false;
    if(symbol->type.id() != ID_struct && symbol->type.id() != ID_union)
      return false;
    for(const auto &component : to_struct_union_type(symbol->type).components())
    {
      if(
        component.type().id() != ID_code &&
        contains_pointer_to_data_member(component.type(), ns, visited))
      {
        return true;
      }
    }
  }
  return false;
}

bool contains_pointer_to_data_member(const typet &type, const namespacet &ns)
{
  std::set<irep_idt> visited;
  return contains_pointer_to_data_member(type, ns, visited);
}

void fix_null_pointers_to_data_members(exprt &expr)
{
#ifdef CPROVER_CPP_ITANIUM_DATA_MEMBER_POINTER_NULL
  for(auto it = expr.depth_begin(), end = expr.depth_end(); it != end;)
  {
    if(
      it->is_constant() && is_pointer_to_data_member_type(it->type()) &&
      to_constant_expr(*it).is_null_pointer())
    {
      it.mutate() = null_pointer_to_data_member(it->type());
      // the replacement has no null pointer constant of its own to visit
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }
#else
  // the workaround encoding's null member pointer value IS the null pointer
  (void)expr;
#endif
}

std::optional<exprt> itanium_abi_cpp_zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  auto value = zero_initializer(type, source_location, ns);
  if(value.has_value() && contains_pointer_to_data_member(type, ns))
    fix_null_pointers_to_data_members(*value);
  return value;
}
