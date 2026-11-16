/*******************************************************************\

Module: Symbolic Execution of havoc_reachable

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Symbolic execution of the havoc_reachable statement, which assigns
/// nondeterministic values to all objects reachable from a set of pointers

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include "goto_symex.h"
#include "path_storage.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>

/// The maximum number of candidate values of a pointer stored in a havocked
/// object.
static const std::size_t max_pointer_candidates = 64;

/// The maximum number of elements of an array whose pointer elements are
/// restricted to candidate values.
static const std::size_t max_array_elements = 64;

/// \return The identifier of the (L1-renamed) object \p object, or the empty
///   identifier if \p object is not a symbol.
static irep_idt object_identifier(const exprt &object)
{
  if(is_ssa_expr(object))
    return remove_level_2(to_ssa_expr(object)).get_identifier();
  if(object.id() == ID_symbol)
    return to_symbol_expr(object).get_identifier();
  return {};
}

/// \return The identifier of the object that the value set entry with
///   identifier \p identifier belongs to: field-sensitive SSA identifiers
///   append "..component" and "[[index]]" to the identifier of the object.
static irep_idt entry_object_identifier(const irep_idt &identifier)
{
  const std::string &s = id2string(identifier);
  const std::size_t pos = std::min(s.find(".."), s.find("[["));
  return pos == std::string::npos ? identifier : irep_idt{s.substr(0, pos)};
}

/// \return True iff objects of type \p type cannot be modified.
static bool is_constant_type(const typet &type)
{
  if(type.get_bool(ID_C_constant))
    return true;
  if(type.id() == ID_array)
    return is_constant_type(to_array_type(type).element_type());
  return false;
}

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
  if(type.id() == ID_struct_tag)
    return !ns.follow_tag(to_struct_tag_type(type)).is_incomplete();
  if(type.id() == ID_union_tag)
    return !ns.follow_tag(to_union_tag_type(type)).is_incomplete();
  return true;
}

/// \return True iff \p type is a pointer to data.
static bool is_data_pointer(const typet &type)
{
  return type.id() == ID_pointer &&
         to_pointer_type(type).base_type().id() != ID_code;
}

/// \return True iff objects of type \p type contain pointers to data.
static bool contains_data_pointer(const typet &type, const namespacet &ns)
{
  if(is_data_pointer(type))
    return true;
  if(type.id() == ID_array)
    return contains_data_pointer(to_array_type(type).element_type(), ns);
  if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    const struct_union_typet &struct_union_type =
      ns.follow_tag(to_struct_or_union_tag_type(type));
    for(const auto &component : struct_union_type.components())
    {
      if(contains_data_pointer(component.type(), ns))
        return true;
    }
  }
  return false;
}

/// Splits \p lvalue into the pointers to data it contains (\p pointers) and
/// the remaining parts (\p others), descending into structs and into arrays
/// of constant size that contain pointers. Unions and other arrays that
/// contain pointers are not split, and are added to \p others.
static void split_lvalue(
  const exprt &lvalue,
  const namespacet &ns,
  std::vector<exprt> &pointers,
  std::vector<exprt> &others)
{
  const typet &type = lvalue.type();
  if(is_data_pointer(type))
    pointers.push_back(lvalue);
  else if(!contains_data_pointer(type, ns))
    others.push_back(lvalue);
  else if(type.id() == ID_struct_tag)
  {
    for(const auto &component :
        ns.follow_tag(to_struct_tag_type(type)).components())
    {
      split_lvalue(member_exprt{lvalue, component}, ns, pointers, others);
    }
  }
  else if(type.id() == ID_array)
  {
    const auto size = numeric_cast<mp_integer>(to_array_type(type).size());
    if(!size.has_value() || *size > max_array_elements)
    {
      others.push_back(lvalue);
      return;
    }
    for(mp_integer i = 0; i < *size; ++i)
    {
      split_lvalue(
        index_exprt{lvalue, from_integer(i, c_index_type())},
        ns,
        pointers,
        others);
    }
  }
  else
    others.push_back(lvalue);
}

/// \return True iff a pointer of type \p candidate may be stored in a pointer
///   of type \p location without changing what kind of object it points to.
static bool is_compatible_pointer(const typet &location, const typet &candidate)
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

/// \return The type of the part of an object of type \p type that \p path
///   denotes, where \p path is a sequence of "..component" and "[[index]]"
///   (as in field-sensitive SSA identifiers) and ".component" and "[]" (as in
///   value set suffixes), or nullptr if \p path cannot be resolved.
static const typet *
type_of_path(const typet &type, const std::string &path, const namespacet &ns)
{
  const typet *current = &type;
  std::size_t pos = 0;
  while(pos < path.size())
  {
    if(path.compare(pos, 2, "[]") == 0 || path.compare(pos, 2, "[[") == 0)
    {
      if(current->id() != ID_array)
        return nullptr;
      const std::size_t end =
        path.compare(pos, 2, "[]") == 0 ? pos + 2 : path.find("]]", pos) + 2;
      if(end < pos + 2)
        return nullptr;
      current = &to_array_type(*current).element_type();
      pos = end;
    }
    else if(path[pos] == '.')
    {
      const std::size_t start =
        path.compare(pos, 2, "..") == 0 ? pos + 2 : pos + 1;
      std::size_t end = start;
      while(end < path.size() && path[end] != '.' && path[end] != '[')
        ++end;
      if(current->id() != ID_struct_tag && current->id() != ID_union_tag)
      {
        return nullptr;
      }
      const struct_union_typet &struct_union_type =
        ns.follow_tag(to_struct_or_union_tag_type(*current));
      const irep_idt name = path.substr(start, end - start);
      if(!struct_union_type.has_component(name))
        return nullptr;
      current = &struct_union_type.get_component(name).type();
      pos = end;
    }
    else
      return nullptr;
  }
  return current;
}

void goto_symext::symex_havoc_reachable(statet &state, const codet &code)
{
  const source_locationt &source_location = state.source.pc->source_location();

  // the objects reachable, in the order they are found
  std::vector<exprt> objects;
  std::unordered_set<irep_idt> known;
  bool unknown_target = false;

  auto add_object = [&objects, &known](const exprt &object)
  {
    if(known.insert(object_identifier(object)).second)
      objects.push_back(object);
  };

  auto add_target = [&add_object, &unknown_target](const exprt &target)
  {
    if(target.id() == ID_unknown)
    {
      unknown_target = true;
      return;
    }
    if(target.id() != ID_object_descriptor)
      return;
    const exprt &root = to_object_descriptor_expr(target).root_object();
    if(root.id() == ID_symbol && root.type().id() != ID_code)
      add_object(root);
    else if(
      root.id() != ID_null_object && root.id() != ID_integer_address &&
      root.id() != ID_string_constant && root.id() != ID_constant &&
      root.type().id() != ID_code)
    {
      unknown_target = true;
    }
  };

  // the objects the operands point to
  for(const auto &operand : code.operands())
  {
    if(operand.type().id() != ID_pointer)
      continue;
    const exprt pointer =
      state.rename<L1>(clean_expr(operand, state, false), ns).get();
    for(const auto &target : state.value_set.get_value_set(pointer, ns))
      add_target(target);
  }

  // the objects that can be named, and the address-taken local variables of
  // all functions on the call stack
  if(code.get_bool(ID_arbitrary_memory))
  {
    std::vector<irep_idt> statics;
    for(const auto &entry : outer_symbol_table.symbols)
    {
      const symbolt &symbol = entry.second;
      if(
        symbol.is_static_lifetime && !symbol.is_type && !symbol.is_macro &&
        symbol.is_lvalue && symbol.type.id() != ID_code &&
        symbol.type.id() != ID_empty && is_complete_type(symbol.type, ns) &&
        !symbol.name.starts_with(CPROVER_PREFIX) &&
        !symbol.base_name.starts_with(CPROVER_PREFIX))
      {
        statics.push_back(symbol.name);
      }
    }
    std::sort(
      statics.begin(),
      statics.end(),
      [](const irep_idt &a, const irep_idt &b)
      { return id2string(a) < id2string(b); });
    for(const auto &name : statics)
    {
      add_object(state.rename<L1>(ns.lookup(name).symbol_expr(), ns).get());
    }

    for(const auto &frame : state.call_stack())
    {
      std::vector<ssa_exprt> locals;
      for(const irep_idt &l1_identifier : frame.local_objects)
      {
        const auto entry = state.get_level2().current_names.find(l1_identifier);
        if(
          entry.has_value() &&
          path_storage.dirty(entry->get().first.get_object_name()))
        {
          locals.push_back(entry->get().first);
        }
      }
      std::sort(
        locals.begin(),
        locals.end(),
        [](const ssa_exprt &a, const ssa_exprt &b) {
          return id2string(a.get_identifier()) < id2string(b.get_identifier());
        });
      for(const auto &local : locals)
        add_object(local);
    }
  }

  // the closure: the objects pointers stored in reachable objects point to
  {
    value_sett::valuest::viewt view;
    state.value_set.values.get_view(view);
    std::unordered_map<irep_idt, std::vector<const value_sett::entryt *>>
      entries;
    for(const auto &item : view)
      entries[entry_object_identifier(item.second.identifier)].push_back(
        &item.second);

    for(std::size_t i = 0; i < objects.size(); ++i)
    {
      const auto it = entries.find(object_identifier(objects[i]));
      if(it == entries.end())
        continue;
      const std::string object_id = id2string(it->first);
      for(const auto *entry : it->second)
      {
        // an unknown value of a non-pointer part of the object is no
        // unknown pointer target
        const typet *type = type_of_path(
          objects[i].type(),
          id2string(entry->identifier).substr(object_id.size()) + entry->suffix,
          ns);
        const bool is_pointer = type == nullptr || type->id() == ID_pointer;
        for(const auto &target : entry->object_map.read())
        {
          const exprt target_expr = state.value_set.to_expr(target);
          if(is_pointer || target_expr.id() != ID_unknown)
            add_target(target_expr);
        }
      }
    }
  }

  std::vector<exprt> havocked;
  for(const auto &object : objects)
  {
    if(!is_constant_type(object.type()))
      havocked.push_back(object);
  }

  // Split the objects into the pointers they contain and the remaining
  // parts. Assigning a nondeterministic pointer would make its value set
  // contain every object in the value set (which is costly to compute, and
  // imprecise), so the pointers are assigned a nondeterministic choice among
  // candidate values instead.
  std::vector<exprt> pointers, others;
  for(const auto &object : havocked)
    split_lvalue(object, ns, pointers, others);

  // record the pointers stored in the objects before changing them
  std::vector<exprt> candidates;
  for(const auto &pointer : pointers)
  {
    // get_fresh_aux_symbol would search the symbol table for each of the
    // (possibly many) temporaries
    const std::string base_name =
      "old_pointer$" +
      std::to_string(path_storage.havoc_reachable_temporaries++);
    auxiliary_symbolt old_value{
      "symex::havoc_reachable::" + base_name, pointer.type(), language_mode};
    old_value.base_name = base_name;
    old_value.location = source_location;
    const symbol_exprt old_value_expr = old_value.symbol_expr();
    const bool inserted =
      state.symbol_table.insert(std::move(old_value)).second;
    CHECK_RETURN(inserted);
    symex_assign(state, old_value_expr, pointer);
    candidates.push_back(old_value_expr);
  }
  for(const auto &object : objects)
  {
    if(object.type().id() == ID_array)
    {
      candidates.push_back(
        address_of_exprt{index_exprt{object, from_integer(0, c_index_type())}});
    }
    else
      candidates.push_back(address_of_exprt{object});
  }

  // the parts that are not pointers
  for(const auto &other : others)
  {
    symex_assign(
      state, other, side_effect_expr_nondett{other.type(), source_location});
  }

  // The statement may store any pointer it can obtain: the pointers stored
  // in the reachable objects, or the addresses of these objects. Restricting
  // the pointers to these values (or null) keeps the value sets, and hence
  // dereferencing, precise. To bound the size of the value sets, each pointer
  // is restricted to at most max_pointer_candidates of them, starting with
  // its own previous value.
  bool too_many_candidates = false;
  for(std::size_t i = 0; i < pointers.size(); ++i)
  {
    const exprt &pointer = pointers[i];
    const typet &type = pointer.type();
    std::vector<const exprt *> chosen{&candidates[i]};
    for(const auto &candidate : candidates)
    {
      if(
        &candidate == &candidates[i] ||
        !is_compatible_pointer(type, candidate.type()))
        continue;
      if(chosen.size() == max_pointer_candidates)
      {
        too_many_candidates = true;
        break;
      }
      chosen.push_back(&candidate);
    }

    exprt value = null_pointer_exprt{to_pointer_type(type)};
    for(auto it = chosen.rbegin(); it != chosen.rend(); ++it)
    {
      value = if_exprt{
        path_storage.build_symex_nondet(bool_typet{}, source_location),
        typecast_exprt::conditional_cast(**it, type),
        std::move(value)};
    }
    symex_assign(state, pointer, value);
  }

  // Unknown targets are common (for example, the pointers stored in memory
  // that is allocated, but not yet written), and mean that the pointer may
  // hold any value, including addresses of objects that are not in the set.
  if(unknown_target)
  {
    log.debug() << "havocking the objects reachable at " << source_location
                << ": some pointers have unknown targets, objects only "
                   "reachable through them keep their values"
                << messaget::eom;
  }

  if(too_many_candidates)
  {
    log.warning() << "havocking the objects reachable at " << source_location
                  << ": some pointers have more than " << max_pointer_candidates
                  << " possible values, and are restricted to "
                  << max_pointer_candidates << " of them" << messaget::eom;
  }
}
