/*******************************************************************\

Module: Objects reachable from a set of pointers

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Objects reachable from a set of pointers

#include "reachable_objects.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/symbol_table_base.h>

#include <algorithm>
#include <set>

/// \return True iff objects of type \p type can be assigned a value as a
///   whole.
static bool is_complete_type(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_code || type.id() == ID_empty)
    return false;
  if(type.id() == ID_array)
  {
    const array_typet &array_type = to_array_type(type);
    return array_type.size().is_not_nil() &&
           is_complete_type(array_type.element_type(), ns);
  }
  if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
    return !ns.follow_tag(to_struct_or_union_tag_type(type)).is_incomplete();
  return true;
}

/// \return True iff \p type is a pointer to data.
static bool is_data_pointer(const typet &type)
{
  return type.id() == ID_pointer &&
         to_pointer_type(type).base_type().id() != ID_code;
}

/// Appends to \p dest the pointers to data within \p lvalue: \p lvalue itself,
/// the members of structs and unions, and the elements of arrays (represented
/// by the element with index 0, as the pointer analyses do not distinguish
/// elements).
static void collect_pointer_lvalues(
  const exprt &lvalue,
  const namespacet &ns,
  std::vector<exprt> &dest)
{
  const typet &type = lvalue.type();
  if(is_data_pointer(type))
    dest.push_back(lvalue);
  else if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    const struct_union_typet &struct_union_type =
      ns.follow_tag(to_struct_or_union_tag_type(type));
    if(struct_union_type.is_incomplete())
      return;
    for(const auto &component : struct_union_type.components())
      collect_pointer_lvalues(member_exprt{lvalue, component}, ns, dest);
  }
  else if(type.id() == ID_array)
  {
    collect_pointer_lvalues(
      index_exprt{lvalue, from_integer(0, c_index_type())}, ns, dest);
  }
}

reachable_objectst find_reachable_objects(
  const std::vector<exprt> &root_pointers,
  const std::vector<exprt> &root_objects,
  const get_pointer_targetst &get_targets,
  const namespacet &ns)
{
  reachable_objectst result;

  std::set<exprt> objects_seen;
  // an object is traversed once for each type it is reached with
  std::set<std::pair<exprt, typet>> traversed;
  std::vector<exprt> worklist;

  auto add_object = [&](const exprt &object, const exprt &view)
  {
    if(objects_seen.insert(object).second)
      result.objects.push_back(object);
    if(traversed.insert({object, view.type()}).second)
      worklist.push_back(view);
  };

  auto follow = [&](const exprt &pointer)
  {
    const typet &base_type = to_pointer_type(pointer.type()).base_type();
    for(const auto &target : get_targets(pointer))
    {
      if(target.id() == ID_unknown)
      {
        result.has_unknown_targets = true;
        continue;
      }
      if(target.id() != ID_object_descriptor)
        continue;
      const exprt &root = to_object_descriptor_expr(target).root_object();
      if(
        root.id() == ID_null_object || root.id() == ID_integer_address ||
        root.id() == ID_string_constant || root.id() == ID_constant ||
        root.type().id() == ID_code)
      {
        continue;
      }
      // Traverse the object directly if it is a symbol of the type it is
      // accessed with, and through the pointer otherwise.
      if(root.id() == ID_symbol && root.type() == base_type)
        add_object(root, root);
      else if(base_type.id() == ID_empty)
        add_object(root, root);
      else
        add_object(root, dereference_exprt{pointer});
    }
  };

  for(const auto &object : root_objects)
    add_object(object, object);
  for(const auto &pointer : root_pointers)
  {
    if(is_data_pointer(pointer.type()))
      follow(pointer);
  }

  while(!worklist.empty())
  {
    const exprt view = worklist.back();
    worklist.pop_back();

    std::vector<exprt> pointers;
    collect_pointer_lvalues(view, ns, pointers);
    for(const auto &pointer : pointers)
    {
      result.pointers.push_back(pointer);
      follow(pointer);
    }
  }

  return result;
}

std::vector<symbol_exprt> static_lifetime_objects(
  const symbol_table_baset &symbol_table,
  const namespacet &ns)
{
  std::vector<symbol_exprt> result;
  for(const auto &entry : symbol_table.symbols)
  {
    const symbolt &symbol = entry.second;
    if(
      symbol.is_static_lifetime && !symbol.is_type && !symbol.is_macro &&
      symbol.is_lvalue && is_complete_type(symbol.type, ns) &&
      !symbol.name.starts_with(CPROVER_PREFIX) &&
      !symbol.base_name.starts_with(CPROVER_PREFIX))
    {
      result.push_back(symbol.symbol_expr());
    }
  }

  std::sort(
    result.begin(),
    result.end(),
    [](const symbol_exprt &a, const symbol_exprt &b)
    { return id2string(a.get_identifier()) < id2string(b.get_identifier()); });

  return result;
}

bool is_compatible_pointer(const typet &location, const typet &candidate)
{
  const typet &location_base = to_pointer_type(location).base_type();
  const typet &candidate_base = to_pointer_type(candidate).base_type();
  auto is_generic = [](const typet &base)
  {
    return base.id() == ID_empty ||
           ((base.id() == ID_signedbv || base.id() == ID_unsignedbv) &&
            to_bitvector_type(base).get_width() == 8);
  };
  return location_base == candidate_base || is_generic(location_base) ||
         is_generic(candidate_base);
}

exprt reachable_pointer_value(
  const exprt &pointer,
  const reachable_objectst &reachable)
{
  const typet &type = pointer.type();
  const nondet_symbol_exprt choice{"value_set::havoc_reachable", bool_typet{}};

  std::vector<exprt> candidates;
  for(const auto &object : reachable.objects)
  {
    exprt address =
      object.type().id() == ID_array
        ? address_of_exprt{index_exprt{object, from_integer(0, c_index_type())}}
        : address_of_exprt{object};
    if(is_compatible_pointer(type, address.type()))
    {
      // Value sets with this many objects make the analyses slow (each of
      // the pointers may point to each of the objects); an unknown target is
      // a sound and compact alternative.
      if(candidates.size() == max_reachable_pointer_candidates)
        return if_exprt{choice, pointer, exprt{ID_unknown, type}};
      candidates.push_back(typecast_exprt::conditional_cast(address, type));
    }
  }

  exprt value = null_pointer_exprt{to_pointer_type(type)};
  for(auto it = candidates.rbegin(); it != candidates.rend(); ++it)
    value = if_exprt{choice, *it, value};

  return if_exprt{choice, pointer, value};
}
