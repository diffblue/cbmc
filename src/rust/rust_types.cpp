/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#include "rust_types.h"

#include <algorithm>
#include <unordered_map>

#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <ansi-c/gcc_types.h>
#include <ansi-c/literals/convert_float_literal.h>
#include <ansi-c/literals/parse_float.h>
#include <util/ieee_float.h>

// TODO Possibly do this in a more efficient way
// TODO This may have to go to the .h file and have "add type" functionality
//   to support user-created types
class type_translatort
{
public:
  typet Translate(std::string const &key)
  {
    if(m_uninitialized)
    {
      Init();
      m_uninitialized = false;
    }

    auto result = m_typeMappings.find(key);
    if(result != m_typeMappings.end())
    {
      return result->second;
    }
    else
    {
      return typet("Unknown Type");
    }
  }

private:
  void Init()
  {
    // TODO add all mappings
    // Actual list of mappings
    m_typeMappings[""] = void_type();
    m_typeMappings["i32"] = signedbv_typet(32);
    m_typeMappings["i64"] = signedbv_typet(64);
    m_typeMappings["u32"] = unsignedbv_typet(32);
    m_typeMappings["u64"] = unsignedbv_typet(64);
    m_typeMappings["f32"] = float_type();
    m_typeMappings["f64"] = double_type();
    m_typeMappings["bool"] = bool_typet();
    m_typeMappings["char"] = char_type();
  }

  bool m_uninitialized = true;
  std::unordered_map<std::string, typet> m_typeMappings;
};

type_translatort translator;

typet rusttype_to_ctype(irep_idt name)
{
  return translator.Translate(name.c_str());
}

/// helper function for checking a pair where order is interchangeable
inline bool pair_is(
  std::string const &a,
  std::string const &b,
  std::string const &s1,
  std::string const &s2)
{
  return (a == s1 && b == s2) || (a == s2 && b == s1);
}

/// resolve two differing rust types if possible, otherwise return empty type
typet rust_resolve_differing_types(exprt &a, exprt &b)
{
  std::string aType(a.type().id().c_str());
  std::string bType(b.type().id().c_str());

  // TODO: Add all resolving types

  // COMP: This assumes widths match, as Rust source code would not compile
  //   if they don't
  if(pair_is(aType, bType, "signedbv", "unsignedbv"))
    return signedbv_typet(to_bitvector_type(a.type()).get_width());

  // mismatched widths -- pick larger -- will have to be more intelligent if
  //   widths > 64 are introduced
  else if(pair_is(aType, bType, "unsignedbv", "unsignedbv"))
  {
    // 32 bit ints need to be changed into 64 bit ints
    a = typecast_exprt(a, unsignedbv_typet(64));
    b = typecast_exprt(b, unsignedbv_typet(64));
    return unsignedbv_typet(64);
  }
  else if(pair_is(aType, bType, "signedbv", "signedbv"))
  {
    // 32 bit ints need to be changed into 64 bit ints
    a = typecast_exprt(a, signedbv_typet(64));
    b = typecast_exprt(b, signedbv_typet(64));
    return signedbv_typet(64);
  }
  else if(pair_is(aType, bType, "floatbv", "floatbv"))
  {
    // 32 bit floats need to be changed into 64 bit floats
    a = typecast_exprt(a, double_type());
    b = typecast_exprt(b, double_type());
    return double_type();
  }

  return typet();
}

typet rust_any_type()
{
  return rust_union_typet(
    {rust_empty_type(), rust_reference_type(), rust_value_type()});
}

typet rust_value_or_empty_type()
{
  return rust_union_typet({rust_value_type(), rust_empty_type()});
}

typet rust_value_or_reference_type()
{
  return rust_union_typet({rust_value_type(), rust_reference_type()});
}

typet rust_value_type()
{
  return rust_union_typet({rust_undefined_type(),
                           rust_null_type(),
                           rust_prim_type(),
                           rust_object_type()});
}

typet rust_prim_type()
{
  return rust_union_typet({floatbv_typet(), string_typet(), bool_typet()});
}

typet rust_reference_type()
{
  return rust_union_typet(
    {rust_member_reference_type(), rust_variable_reference_type()});
}

typet rust_member_reference_type()
{
  return typet("rust_member_reference_type");
}

typet rust_variable_reference_type()
{
  return typet("rust_variable_reference_type");
}

typet rust_object_type()
{
  return rust_union_typet(
    {rust_user_object_type(), rust_builtin_object_type()});
}

typet rust_user_object_type()
{
  return typet("rust_user_object_type");
}

typet rust_builtin_object_type()
{
  return typet("rust_builtin_object_type");
}

typet rust_null_type()
{
  return typet("rust_null_type");
}

typet rust_undefined_type()
{
  return typet("rust_undefined_type");
}

typet rust_kind()
{
  return typet("rust_kind");
}

typet rust_empty_type()
{
  return typet("rust_empty_type");
}

bool rust_is_subtype(const typet &type1, const typet &type2)
{
  if(type2.id() == ID_union)
  {
    const rust_union_typet &type2_union = to_rust_union_type(type2);

    if(type1.id() == ID_union)
      return to_rust_union_type(type1).is_subtype(type2_union);
    else
      return rust_union_typet(type1).is_subtype(type2_union);
  }
  else
    return type1.id() == type2.id();
}

bool rust_incompatible_types(const typet &type1, const typet &type2)
{
  return rust_union_typet(type1)
    .intersect_with(rust_union_typet(type2))
    .components()
    .empty();
}

typet rust_union(const typet &type1, const typet &type2)
{
  return rust_union_typet(type1).union_with(rust_union_typet(type2)).to_type();
}

bool is_empty_type(typet const &type)
{
  return type.id() == ID_empty || type.id().empty();
}

static bool compare_components(
  const union_typet::componentt &comp1,
  const union_typet::componentt &comp2)
{
  return comp1.type().id() < comp2.type().id();
}

rust_union_typet::rust_union_typet(const std::vector<typet> &types)
  : union_typet()
{
  auto &elements = components();
  for(const auto &type : types)
  {
    if(type.id() == ID_union)
    {
      for(const auto &component : to_union_type(type).components())
        elements.push_back(component);
    }
    else
      elements.push_back(componentt(ID_anonymous, type));
  }

  std::sort(elements.begin(), elements.end(), compare_components);
}

rust_union_typet
rust_union_typet::union_with(const rust_union_typet &other) const
{
  auto &elements1 = components();
  auto &elements2 = other.components();
  rust_union_typet result;
  auto &elements = result.components();
  elements.resize(elements1.size() + elements2.size());
  std::vector<union_typet::componentt>::iterator it = std::set_union(
    elements1.begin(),
    elements1.end(),
    elements2.begin(),
    elements2.end(),
    elements.begin(),
    compare_components);
  elements.resize(it - elements.begin());

  return result;
}

rust_union_typet
rust_union_typet::intersect_with(const rust_union_typet &other) const
{
  auto &elements1 = components();
  auto &elements2 = other.components();
  rust_union_typet result;
  auto &elements = result.components();
  elements.resize(std::min(elements1.size(), elements2.size()));
  std::vector<union_typet::componentt>::iterator it = std::set_intersection(
    elements1.begin(),
    elements1.end(),
    elements2.begin(),
    elements2.end(),
    elements.begin(),
    compare_components);
  elements.resize(it - elements.begin());

  return result;
}

bool rust_union_typet::is_subtype(const rust_union_typet &other) const
{
  auto it = components().begin();
  auto it2 = other.components().begin();
  while(it < components().end())
  {
    if(it2 >= other.components().end())
    {
      // We haven't found all types, but the second array finishes
      return false;
    }

    if(it->type().id() == it2->type().id())
    {
      // Found the type
      it++;
      it2++;
    }
    else if(it->type().id() < it2->type().id())
    {
      // Missing type
      return false;
    }
    else // it->type().id()>it2->type().id()
    {
      // Skip one element in the second array
      it2++;
    }
  }

  return true;
}

const typet &rust_union_typet::to_type() const
{
  auto &elements = components();
  if(elements.size() == 1)
    return elements[0].type();

  return *this;
}
