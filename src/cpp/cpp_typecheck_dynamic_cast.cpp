/*******************************************************************\

Module: C++ Language Type Checking

Author: Kiro

\*******************************************************************/

/// \file
/// C++ Language Type Checking: the run-time check of dynamic_cast

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

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
/// with a unique A subobject, the most derived object is a D object iff the
/// virtual table pointer of *v holds the value a complete D object installs
/// for its A subobject ([class.virtual]); the result is then a pointer to
/// D's unique public C subobject, or null if D has none (/9.3, /10).  A
/// null v yields null (/4).  For a vtable pointer matching no class of the
/// translation unit (an object of a class defined elsewhere), the result is
/// a nondeterministic choice between the unadjusted pointer and null.
/// \return the expression replacing \p check, or nil if a class involved has
///   a layout this does not handle (virtual bases, repeated subobjects)
exprt cpp_typecheckt::runtime_dynamic_cast(const exprt &check)
{
  const exprt &v = to_unary_expr(check).op();
  const pointer_typet &result_type = to_pointer_type(check.type());
  const irep_idt a_tag =
    to_struct_tag_type(to_pointer_type(v.type()).base_type()).get_identifier();
  const irep_idt c_tag =
    to_struct_tag_type(result_type.base_type()).get_identifier();
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
    // (a class with several A subobjects, or one in a virtual base, is not
    // handled: give up on the cast)
    if(a_subobjects.size() != 1 || !a_subobjects.front().virtual_base.empty())
      return nil_exprt{};
    // [expr.dynamic.cast]/9: v must point to a public base subobject
    if(!base_publicly_accessible(d_struct, a_struct))
      continue;
    const mp_integer a_offset = a_subobjects.front().offset;
    const auto *d_vptr =
      vtable_pointer_at(d_struct, a_offset + a_vptr_offset, ns);
    if(d_vptr == nullptr)
      return nil_exprt{};
    const exprt vptr_value = vtable_pointer_value(d_symbol, *d_vptr);
    if(vptr_value.is_nil())
      return nil_exprt{};
    const exprt is_d = equal_exprt{
      v_vptr, typecast_exprt::conditional_cast(vptr_value, v_vptr.type())};

    exprt result = null_pointer_exprt{result_type};
    const auto c_subobjects = base_subobjects(d_struct, c_tag);
    const symbolt &c_symbol = lookup(c_tag);
    // several C subobjects (/9.1 then depends on which one contains *v) or
    // one in a virtual base: not handled
    if(
      c_subobjects.size() > 1 ||
      (c_subobjects.size() == 1 && !c_subobjects.front().virtual_base.empty()))
    {
      return nil_exprt{};
    }
    if(
      c_subobjects.size() == 1 &&
      base_publicly_accessible(d_struct, to_struct_type(c_symbol.type)))
    {
      // the C subobject of the D object
      const mp_integer delta = c_subobjects.front().offset - a_offset;
      const pointer_typet byte_pointer = pointer_type(unsigned_char_type());
      result = typecast_exprt{
        plus_exprt{
          typecast_exprt{v, byte_pointer},
          from_integer(delta, signed_size_type())},
        result_type};
    }
    cases.emplace_back(is_d, result);
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
void cpp_typecheckt::resolve_runtime_dynamic_casts(exprt &expr)
{
  for(auto &op : expr.operands())
    resolve_runtime_dynamic_casts(op);
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
      has_subexpr(entry.second.value, ID_cpp_runtime_dynamic_cast))
    {
      names.push_back(entry.first);
    }
  }
  for(const auto &name : names)
    resolve_runtime_dynamic_casts(symbol_table.get_writeable_ref(name).value);
}
