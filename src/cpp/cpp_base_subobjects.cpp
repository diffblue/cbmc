/*******************************************************************\

Module: C++ Language Type Checking

Author: Kiro

\*******************************************************************/

/// \file
/// Base class subobjects of a flattened class layout

#include <util/pointer_offset_size.h>

#include "cpp_typecheck.h"

#include <map>

/// Whether \p component occupies storage in the flattened layout (the layout
/// ignores member functions, static members and member types).
static bool is_storage(const struct_typet::componentt &component)
{
  return component.type().id() != ID_code &&
         !component.get_bool(ID_is_static) && !component.get_bool(ID_is_type);
}

std::vector<cpp_typecheckt::base_subobjectt> cpp_typecheckt::base_subobjects(
  const struct_typet &derived,
  const irep_idt &base)
{
  // N5008 [class.mi]/4: each distinct occurrence of a non-virtual base class
  // in the class lattice of the most derived class is a distinct subobject,
  // each virtual base class a single one.  add_base_components records on
  // every flattened component the path of base classes through which it is
  // reached (#subobject_path, starting at a direct base of `derived' or at
  // the virtual base that contains it); a subobject of `base' is a path
  // prefix ending in `base', and it starts at its first storage component.
  std::vector<base_subobjectt> result;
  if(derived.get(ID_name) == base)
  {
    result.push_back({{}, 0, irep_idt{}});
    return result;
  }
  const namespacet ns{symbol_table};
  std::map<std::vector<irep_idt>, std::size_t> index_of;
  for(const auto &component : derived.components())
  {
    const auto &steps = component.find(ID_C_subobject_path).get_sub();
    if(steps.empty() || !is_storage(component) || component.get_is_padding())
      continue;
    std::vector<irep_idt> prefix;
    for(const auto &step : steps)
    {
      prefix.push_back(step.id());
      if(step.id() != base)
        continue;
      const auto offset = member_offset(derived, component.get_name(), ns);
      if(!offset.has_value())
        continue;
      const auto it = index_of.find(prefix);
      if(it == index_of.end())
      {
        index_of.emplace(prefix, result.size());
        result.push_back({prefix, *offset, component.get(ID_C_virtual_base)});
      }
      else if(*offset < result[it->second].offset)
        result[it->second].offset = *offset;
    }
  }
  return result;
}
