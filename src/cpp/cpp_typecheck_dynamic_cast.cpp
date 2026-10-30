/*******************************************************************\

Module: C++ Language Type Checking

Author: Kiro

\*******************************************************************/

/// \file
/// C++ Language Type Checking: the run-time check of dynamic_cast

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

#include <algorithm>

/// The vtable pointer component of class \p cls at byte offset \p offset,
/// or nullptr.
static const struct_typet::componentt *vtable_pointer_at(
  const struct_typet &cls,
  const mp_integer &offset,
  const namespacet &ns)
{
  for(const auto &c : cls.components())
  {
    if(!c.get_bool(ID_is_vtptr))
      continue;
    const auto o = member_offset(cls, c.get_name(), ns);
    if(o.has_value() && *o == offset)
      return &c;
  }
  return nullptr;
}

/// N5008 [expr.dynamic.cast]/9: `dynamic_cast<C *>(v)' for a pointer v to a
/// polymorphic class A, C not a base of A.  The result depends on the most
/// derived object v points into.  For each class D of the translation unit
/// and each of its A subobjects (also within virtual bases: their offsets in
/// a complete D object are fixed), v points to that subobject of a D object
/// iff its vtable pointer holds the value a complete D installs there
/// ([class.virtual]); the result is then the C object derived from that
/// subobject (/9.1), else D's unique public C base (/9.2), else null (/9.3,
/// /10).  A
/// null v yields null (/4).  For a vtable pointer matching no class of the
/// translation unit (an object of a class defined elsewhere), the result is
/// a nondeterministic choice between the unadjusted pointer and null.
/// \return the expression replacing \p check, or nil if subobjects cannot be
///   told apart by their vtable pointers
exprt cpp_typecheckt::runtime_dynamic_cast(const exprt &check)
{
  const exprt &v = to_unary_expr(check).op();
  const pointer_typet &result_type = to_pointer_type(check.type());
  const irep_idt a_tag =
    to_struct_tag_type(to_pointer_type(v.type()).base_type()).get_identifier();
  // [expr.dynamic.cast]/8: to `void *', the most derived object itself
  const bool to_most_derived = result_type.base_type().id() == ID_empty;
  const irep_idt c_tag =
    to_most_derived
      ? irep_idt{}
      : to_struct_tag_type(result_type.base_type()).get_identifier();
  const namespacet ns{symbol_table};

  const symbolt &a_symbol = lookup(a_tag);
  const struct_typet &a_struct = to_struct_type(a_symbol.type);
  // the vtable pointer of the A subobject: A's first one
  const struct_typet::componentt *a_vptr = nullptr;
  mp_integer a_vptr_offset = 0;
  for(const auto &c : a_struct.components())
  {
    if(!c.get_bool(ID_is_vtptr))
      continue;
    const auto o = member_offset(a_struct, c.get_name(), ns);
    if(o.has_value() && (a_vptr == nullptr || *o < a_vptr_offset))
    {
      a_vptr = &c;
      a_vptr_offset = *o;
    }
  }
  if(a_vptr == nullptr)
    return nil_exprt{};

  const source_locationt &location = check.source_location();
  const exprt v_vptr = member_exprt{
    dereference_exprt{v, struct_tag_typet{a_tag}},
    a_vptr->get_name(),
    a_vptr->type()};

  // the cases, one per candidate most derived class
  std::vector<std::pair<exprt, exprt>> cases;
  for(const auto &entry : symbol_table)
  {
    const symbolt &d_symbol = entry.second;
    if(
      !d_symbol.is_type || d_symbol.type.id() != ID_struct ||
      to_struct_type(d_symbol.type).is_incomplete())
    {
      continue;
    }
    const struct_typet &d_struct = to_struct_type(d_symbol.type);
    const auto a_subobjects = base_subobjects(d_struct, a_tag);
    if(a_subobjects.empty())
      continue;
    // [expr.dynamic.cast]/9: v must point to a public base subobject (not
    // for the cast to `void *', /8)
    if(!to_most_derived && !base_publicly_accessible(d_struct, a_struct))
      continue;
    const auto c_subobjects = to_most_derived
                                ? std::vector<base_subobjectt>{}
                                : base_subobjects(d_struct, c_tag);
    const bool c_public =
      to_most_derived ||
      base_publicly_accessible(d_struct, to_struct_type(lookup(c_tag).type));
    // In a complete D object every subobject, also one within a virtual
    // base, is at a fixed offset (base_subobjects gives the offsets in D's
    // complete layout), so each A subobject is a case of its own,
    // recognized by the value D installs in its vtable pointer.
    std::vector<exprt> values_seen;
    for(const auto &a_subobject : a_subobjects)
    {
      const mp_integer a_offset = a_subobject.offset;
      const auto *d_vptr =
        vtable_pointer_at(d_struct, a_offset + a_vptr_offset, ns);
      if(d_vptr == nullptr)
        return nil_exprt{};
      const exprt vptr_value = vtable_pointer_value(d_symbol, *d_vptr);
      if(vptr_value.is_nil())
        return nil_exprt{};
      // two A subobjects sharing a table cannot be told apart
      for(const auto &seen : values_seen)
      {
        if(seen == vptr_value)
          return nil_exprt{};
      }
      values_seen.push_back(vptr_value);
      const exprt is_d = equal_exprt{
        v_vptr, typecast_exprt::conditional_cast(vptr_value, v_vptr.type())};

      // /9.1: the C objects derived from this A subobject -- C is the most
      // derived class itself, or a C subobject whose base path leads to
      // this A subobject; /9.2: otherwise D's unique public C base
      std::vector<mp_integer> derived_from_a;
      for(const auto &c_subobject : c_subobjects)
      {
        const bool contains =
          c_subobject.path.empty() ||
          (c_subobject.virtual_base == a_subobject.virtual_base &&
           c_subobject.path.size() <= a_subobject.path.size() &&
           std::equal(
             c_subobject.path.begin(),
             c_subobject.path.end(),
             a_subobject.path.begin()));
        if(contains)
          derived_from_a.push_back(c_subobject.offset);
      }
      std::optional<mp_integer> c_offset;
      if(to_most_derived)
        c_offset = 0;
      else if(derived_from_a.size() == 1 && c_public)
        c_offset = derived_from_a.front();
      else if(derived_from_a.empty() && c_subobjects.size() == 1 && c_public)
        c_offset = c_subobjects.front().offset;

      exprt result = null_pointer_exprt{result_type};
      if(c_offset.has_value())
      {
        const pointer_typet byte_pointer = pointer_type(unsigned_char_type());
        result = typecast_exprt{
          plus_exprt{
            typecast_exprt{v, byte_pointer},
            from_integer(*c_offset - a_offset, signed_size_type())},
          result_type};
      }
      cases.emplace_back(is_d, result);
    }
  }

  // an object of a class the translation unit does not define
  exprt otherwise = if_exprt{
    side_effect_expr_nondett{bool_typet{}, location},
    typecast_exprt{v, result_type},
    null_pointer_exprt{result_type}};
  for(auto it = cases.rbegin(); it != cases.rend(); ++it)
    otherwise = if_exprt{it->first, it->second, otherwise};
  exprt result = if_exprt{
    equal_exprt{v, null_pointer_exprt{to_pointer_type(v.type())}},
    null_pointer_exprt{result_type},
    otherwise};
  result.add_source_location() = location;
  return result;
}

/// Replace every `cpp_runtime_dynamic_cast' in \p expr (see
/// dynamic_typecast) by its run-time check.
/// Whether \p expr contains a `cpp_runtime_dynamic_cast', also as the
/// deallocated object of a delete-expression
static bool has_runtime_dynamic_cast(const exprt &expr)
{
  if(expr.id() == ID_cpp_runtime_dynamic_cast)
    return true;
  const irept &deallocated = expr.find("#deallocated_object");
  if(deallocated.is_not_nil())
    return true;
  for(const auto &op : expr.operands())
    if(has_runtime_dynamic_cast(op))
      return true;
  return false;
}

void cpp_typecheckt::resolve_runtime_dynamic_casts(exprt &expr)
{
  for(auto &op : expr.operands())
    resolve_runtime_dynamic_casts(op);
  // a delete-expression's deallocated object (typecheck_expr_delete), a
  // named sub-expression
  if(expr.find("#deallocated_object").is_not_nil())
    resolve_runtime_dynamic_casts(
      static_cast<exprt &>(expr.add("#deallocated_object")));
  if(expr.id() != ID_cpp_runtime_dynamic_cast)
    return;
  exprt resolved = runtime_dynamic_cast(expr);
  if(resolved.is_nil())
  {
    // the previous model: a sound over-approximation of both outcomes
    const exprt &v = to_unary_expr(expr).op();
    resolved = if_exprt{
      side_effect_expr_nondett{bool_typet{}, expr.source_location()},
      typecast_exprt{v, expr.type()},
      null_pointer_exprt{to_pointer_type(expr.type())}};
    resolved.add_source_location() = expr.source_location();
  }
  expr = std::move(resolved);
}

void cpp_typecheckt::resolve_runtime_dynamic_casts()
{
  std::vector<irep_idt> names;
  for(const auto &entry : symbol_table)
  {
    if(
      !entry.second.is_type && entry.second.value.is_not_nil() &&
      has_runtime_dynamic_cast(entry.second.value))
    {
      names.push_back(entry.first);
    }
  }
  for(const auto &name : names)
    resolve_runtime_dynamic_casts(symbol_table.get_writeable_ref(name).value);
}
