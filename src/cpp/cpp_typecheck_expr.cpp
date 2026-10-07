/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/floatbv_expr.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_constexpr_eval.h"
#include "cpp_exception_id.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_qualifiers.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"
#include "expr2cpp.h"
#include "itanium_abi_cpp_zero_initializer.h"

#include <functional>
#include <optional>

bool cpp_typecheckt::find_parent(
  const symbolt &symb,
  const irep_idt &base_name,
  irep_idt &identifier)
{
  for(const auto &b : to_struct_type(symb.type).bases())
  {
    const irep_idt &id = b.type().get_identifier();
    if(lookup(id).base_name == base_name)
    {
      identifier = id;
      return true;
    }
  }

  return false;
}

/// Phase 1B target-typet overload — currently forwards to the
/// no-target implementation.  Subsequent phases consume the target
/// to drive [temp.deduct.funcaddr]/1 deduction at the address-of
/// and cpp_name layers.
void cpp_typecheckt::typecheck_expr_main(
  exprt &expr,
  const target_typet &target)
{
  (void)target;
  typecheck_expr_main(expr);
}

bool cpp_typecheckt::requirement_expression_is_valid(exprt op)
{
  // [expr.prim.req.general]/5: substitution into / semantic checking of a
  // requirement that forms an invalid expression in the immediate context
  // makes the requires-expression evaluate to false, not ill-formed.  Some
  // typecheck paths report the failure by throwing (caught here); others emit
  // a diagnostic and return without throwing (e.g. member access on a
  // non-class type).  Capture and restore the error count so that either kind
  // of failure becomes a soft `false` and does not fail the translation unit.
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  bool valid = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    // N5008 [temp.variadic]/5 + [expr.prim.req]/2: the requirement is
    // checked with the constrained declaration's parameter mapping,
    // including PACK bindings.  A call-argument (or new-initializer)
    // pack expansion over an EMPTY pack must disappear before
    // typechecking -- without this, `::new((void*)0)
    // _Tp(declval<_Args>()...)` with _Args deduced empty (value-
    // initialization through std::construct_at) kept the unexpanded
    // scalar `declval<_Args>()`, its resolution threw on the unbound
    // pack parameter, and the whole candidate was removed: the CALLER's
    // body then failed to convert and was silently dropped
    // (gcc-16 <optional>'s _M_apply, reduced to a 30-line kernel).
    expand_requires_parameter_packs(op);
    template_map.expand_call_argument_packs(op);
    // [expr.prim.req.general]/2: the expressions of a requires-expression
    // are unevaluated operands -- nothing they name is odr-used
    unevaluated_operandt unevaluated_guard{*this};
    typecheck_expr(op);
  }
  catch(...)
  {
    valid = false;
  }
  if(
    get_message_handler().get_message_count(messaget::M_ERROR) != errors_before)
    valid = false;
  get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  return valid;
}

/// Expand the call-argument pack expansions in \p expr that name a
/// requires-expression parameter pack (bind_requires_parameter_pack),
/// before the template packs alone are expanded (expand_call_argument_packs,
/// which would leave the parameter pack's name in each element).
void cpp_typecheckt::expand_requires_parameter_packs(exprt &expr)
{
  if(requires_parameter_packs.empty())
    return;
  for(auto &op : expr.operands())
    expand_requires_parameter_packs(op);
  if(expr.id() == ID_side_effect && expr.get(ID_statement) == ID_function_call)
  {
    for(auto &op : expr.operands())
      if(op.id() == ID_arguments)
        expand_type_pack_arguments(op, /*with_requires_parameters=*/true);
  }
}

/// A fresh symbol for an element of the parameter pack \p name, of type
/// \p element_type, as an lvalue expression (implicitly dereferenced for a
/// reference type: a reference names the object it refers to,
/// [expr.type]/1).
exprt cpp_typecheckt::requires_parameter_pack_element(
  const irep_idt &name,
  const typet &element_type)
{
  static std::size_t pack_counter = 0;
  symbolt element{
    "requires_param::" + id2string(name) + "#pack" +
      std::to_string(pack_counter++),
    element_type,
    ID_cpp};
  element.base_name = name;
  element.is_lvalue = true;
  symbol_table.add(element);
  exprt element_expr = element.symbol_expr();
  element_expr.set(ID_C_lvalue, true);
  add_implicit_dereference(element_expr);
  return element_expr;
}

/// expand_requires_parameter_packs in the decltype operands of \p type
/// (a trailing return type naming a function parameter pack).
void cpp_typecheckt::expand_requires_parameter_packs_in_type(irept &type)
{
  if(requires_parameter_packs.empty())
    return;
  if(type.id() == ID_decltype)
  {
    expand_requires_parameter_packs(
      static_cast<exprt &>(type.add(ID_expr_arg)));
    return;
  }
  for(auto &sub : type.get_sub())
    expand_requires_parameter_packs_in_type(sub);
  for(auto &named : type.get_named_sub())
    expand_requires_parameter_packs_in_type(named.second);
}

/// N5008 [expr.prim.req.general]/4, [temp.variadic]/5: a parameter of a
/// requires-expression may be a function parameter pack, `A &&...a'; it
/// declares one parameter per element of the template parameter pack A, the
/// k-th of type A_k &&.  If \p type (in parsed form, with the template map of
/// the enclosing instantiation) is such a pack expansion, bind one symbol per
/// element, record them for the expansion of `...' patterns naming \p name
/// (expand_type_pack_arguments) and return true; otherwise return false.
bool cpp_typecheckt::bind_requires_parameter_pack(
  const irep_idt &name,
  const typet &type)
{
  if(!type.get_bool(ID_ellipsis))
  {
    requires_parameter_packs.erase(name);
    return false;
  }
  // the class/function template packs the pattern names
  std::set<irep_idt> packs;
  std::function<void(const irept &)> collect = [&](const irept &n)
  {
    if(n.id() == ID_name)
    {
      const std::string id = id2string(n.get(ID_identifier));
      for(const auto &entry : template_map.pack_size_map)
      {
        const std::string key = id2string(entry.first);
        const auto sep = key.rfind("::");
        if((sep == std::string::npos ? key : key.substr(sep + 2)) == id)
          packs.insert(entry.first);
      }
    }
    for(const auto &sub : n.get_sub())
      collect(sub);
    for(const auto &named : n.get_named_sub())
      collect(named.second);
  };
  collect(type);
  if(packs.empty())
    return false;
  const std::size_t size =
    template_map.pack_size_map.find(*packs.begin())->second;
  for(const auto &pack : packs)
    if(template_map.pack_size_map.find(pack)->second != size)
      return false;
  std::vector<exprt> elements;
  for(std::size_t k = 0; k < size; ++k)
  {
    template_mapt element_map = template_map;
    for(const auto &pack : packs)
    {
      const auto it = template_map.pack_args_map.find(pack);
      if(it == template_map.pack_args_map.end() || it->second.size() != size)
        return false;
      // the k-th element, as a scalar binding (a pack name is otherwise
      // never substituted outside an expansion)
      element_map.type_map[pack] = it->second[k];
      element_map.pack_args_map.erase(pack);
      element_map.pack_size_map.erase(pack);
    }
    typet element_type = type;
    element_type.remove(ID_ellipsis);
    element_map.apply(element_type);
    try
    {
      sfinae_contextt sfinae_guard{*this};
      typecheck_type(element_type);
    }
    catch(...)
    {
      return false;
    }
    elements.push_back(requires_parameter_pack_element(name, element_type));
  }
  requires_parameter_packs[name] = std::move(elements);
  return true;
}

void cpp_typecheckt::bind_requires_parameter(
  const irep_idt &name,
  const typet &type)
{
  static std::size_t binding_counter = 0;
  const irep_idt id = "requires_param::" + id2string(name) + "#" +
                      std::to_string(binding_counter++);
  symbolt param_sym{id, type, ID_cpp};
  param_sym.base_name = name;
  param_sym.is_lvalue = true;
  symbol_table.add(param_sym);
  // A scope's entries form a multimap: a second `__i` next to the one bound
  // by an earlier requires-expression evaluated in the same scope made the
  // name ambiguous and the requirement silently unsatisfied.  Rebind the
  // existing entry instead.
  cpp_scopet &scope = cpp_scopes.current_scope();
  for(cpp_idt *existing : scope.lookup(name, cpp_scopet::SCOPE_ONLY))
  {
    if(
      existing->id_class == cpp_idt::id_classt::SYMBOL &&
      has_prefix(id2string(existing->identifier), "requires_param::"))
    {
      existing->identifier = id;
      return;
    }
  }
  cpp_idt &scope_id = scope.insert(name);
  scope_id.identifier = id;
  scope_id.id_class = cpp_idt::id_classt::SYMBOL;
}

/// N5008 [class.prop]/1: a trivially copyable class has at least one eligible
/// copy constructor, move constructor, copy assignment operator or move
/// assignment operator, each of which is trivial (implicitly declared, not
/// user-provided, [class.copy.ctor]/11, [class.copy.assign]/9), no
/// non-trivial ones, and a trivial non-deleted destructor; and, transitively
/// ([class.copy.ctor]/11), no virtual functions or virtual bases, and bases
/// and non-static data members of trivially copyable type.  /2: a trivial
/// class is trivially copyable and has a trivial default constructor
/// ([class.default.ctor]/3: no user-provided one, no default member
/// initializers, bases and members trivial).  [basic.types.general]/9
/// extends both to scalars, arrays and cv-qualified versions.
/// N5008 [class.prop], [class.virtual]/1, [class.dtor]/9, [dcl.init.aggr]/1:
/// the class properties behind the GCC/Clang type traits `__is_empty',
/// `__is_polymorphic', `__has_virtual_destructor', `__is_standard_layout',
/// `__is_pod', `__is_aggregate', `__is_literal_type' for the type \p t.
bool cpp_typecheckt::class_property(const irep_idt &trait, const typet &t)
{
  const bool is_class = t.id() == ID_struct_tag;
  const bool is_union = t.id() == ID_union_tag;
  if(t.id() == ID_array)
  {
    // [dcl.init.aggr]/1: an array is an aggregate; for the properties
    // defined over "possibly cv-qualified class type or array thereof" an
    // array has the property of its element type
    if(trait == "__is_aggregate")
      return true;
    if(
      trait == "__is_standard_layout" || trait == "__is_pod" ||
      trait == "__is_literal_type")
    {
      return class_property(trait, to_array_type(t).element_type());
    }
    return false;
  }
  if(!is_class && !is_union)
  {
    // scalars: standard-layout, POD, literal; not empty/polymorphic/aggregate
    if(trait == "__is_empty" || trait == "__is_polymorphic")
      return false;
    if(trait == "__has_virtual_destructor" || trait == "__is_aggregate")
      return false;
    if(t.id() == ID_empty)
      return trait == "__is_literal_type"; // void is a literal type
    return t.id() != ID_code;              // a function type has none of them
  }
  // N5008 [meta.unary.prop]/3: the type must be complete -- a class
  // template specialization named but not yet elaborated (`equal_to<void>'
  // inside `__by_ref_or_value_fn<equal_to<>>' while instantiating
  // std::find) is completed here, otherwise it reads as a class with no
  // members and, e.g., NOT empty.
  elaborate_class_template(t);
  const struct_union_typet &su = is_class
                                   ? static_cast<const struct_union_typet &>(
                                       follow_tag(to_struct_tag_type(t)))
                                   : static_cast<const struct_union_typet &>(
                                       follow_tag(to_union_tag_type(t)));
  if(su.get_bool(ID_incomplete))
    return false;

  bool has_vtptr = false, has_virtual_dtor = false, has_virtual_base = false,
       has_data_member = false, has_reference_member = false,
       has_user_ctor = false, has_nontrivial_dtor = false,
       has_private_member = false, has_public_member = false,
       has_default_member_init = false, all_members_ok = true;
  if(is_class)
  {
    for(const auto &base : to_struct_type(su).bases())
    {
      if(base.get_bool(ID_virtual))
        has_virtual_base = true;
      const typet &base_type = static_cast<const typet &>(base.find(ID_type));
      if(trait == "__is_polymorphic" && class_property(trait, base_type))
        has_vtptr = true;
      if(
        (trait == "__is_standard_layout" || trait == "__is_pod" ||
         trait == "__is_literal_type") &&
        !class_property(trait, base_type))
      {
        all_members_ok = false;
      }
    }
  }
  for(const auto &comp : su.components())
  {
    if(comp.get_bool(ID_is_static) || comp.get_bool(ID_is_type))
      continue;
    if(comp.get_bool(ID_is_vtptr))
    {
      has_vtptr = true;
      continue;
    }
    if(comp.get_is_padding())
      continue;
    if(comp.type().id() == ID_code)
    {
      const code_typet &code_type = to_code_type(comp.type());
      const irep_idt &return_id = code_type.return_type().id();
      if(return_id == ID_destructor)
      {
        if(comp.get_bool(ID_is_virtual))
          has_virtual_dtor = true;
        if(!code_type.get_bool("#is_implicit_dtor"))
          has_nontrivial_dtor = true;
      }
      else if(return_id == ID_constructor)
      {
        if(!code_type.get_bool("#is_implicit_ctor"))
          has_user_ctor = true;
      }
      if(comp.get_bool(ID_is_virtual))
        has_vtptr = true;
      continue;
    }
    // a non-static data member (own or from a base)
    has_data_member = true;
    if(comp.find(ID_value).is_not_nil())
      has_default_member_init = true;
    if(is_reference(comp.type()) || is_rvalue_reference(comp.type()))
      has_reference_member = true;
    if(comp.get_access() == ID_private || comp.get_access() == ID_protected)
      has_private_member = true;
    else
      has_public_member = true;
    if(
      (trait == "__is_standard_layout" || trait == "__is_pod" ||
       trait == "__is_literal_type") &&
      !class_property(trait, comp.type()))
    {
      all_members_ok = false;
    }
  }

  if(trait == "__is_empty")
  {
    // [meta.unary.prop]: a class type, but not a union type, with no
    // non-static data members other than subobjects of zero size, no
    // virtual member functions, no virtual base classes, and no base class
    // B for which is_empty_v<B> is false
    return is_class && !has_data_member && !has_vtptr && !has_virtual_base;
  }
  if(trait == "__is_polymorphic")
    return is_class && has_vtptr; // [class.virtual]/1
  if(trait == "__has_virtual_destructor")
    return has_virtual_dtor; // [class.dtor]/9
  if(trait == "__is_standard_layout")
  {
    // [class.prop]/3 (simplified: no virtual functions or bases, uniform
    // access control, standard-layout members and bases, no reference
    // members)
    return !has_vtptr && !has_virtual_base && !has_reference_member &&
           !(has_private_member && has_public_member) && all_members_ok;
  }
  if(trait == "__is_pod")
  {
    // [depr.meta.types]: standard-layout and trivial
    return class_property("__is_standard_layout", t) &&
           is_trivially_copyable_type(t, true, 64);
  }
  if(trait == "__is_aggregate")
  {
    // [dcl.init.aggr]/1: no user-declared or inherited constructors, no
    // private or protected direct non-static data members, no virtual
    // functions, no virtual, private or protected base classes
    bool private_base = false;
    if(is_class)
    {
      for(const auto &base : to_struct_type(su).bases())
        if(base.get(ID_access) != ID_public)
          private_base = true;
    }
    return !has_user_ctor && !has_private_member && !has_vtptr &&
           !has_virtual_base && !private_base;
  }
  if(trait == "__is_literal_type")
  {
    // [basic.types.general]/10: trivial destructor, every member of
    // literal type, and an aggregate or at least one constexpr constructor
    // (the latter not tracked: any constructor counts)
    (void)has_default_member_init;
    return !has_nontrivial_dtor && !has_virtual_dtor && all_members_ok;
  }
  return false;
}

bool cpp_typecheckt::is_trivially_copyable_type(
  const typet &type,
  bool want_trivial,
  int depth)
{
  if(depth <= 0)
    return false;
  if(type.id() == ID_array)
    return is_trivially_copyable_type(
      to_array_type(type).element_type(), want_trivial, depth - 1);
  if(type.id() == ID_struct_tag)
  {
    const struct_typet &st = follow_tag(to_struct_tag_type(type));
    if(st.get_bool(ID_incomplete))
      return false;
    for(const auto &base : st.bases())
    {
      if(base.get_bool(ID_virtual))
        return false;
      const typet &base_type = static_cast<const typet &>(base.find(ID_type));
      if(!is_trivially_copyable_type(base_type, want_trivial, depth - 1))
        return false;
    }
    // [class.default.ctor]/3, [class.prop]/2: a trivial class HAS a
    // trivial default constructor.  A class with a user-declared
    // constructor of another signature (`S(int)') has no implicit default
    // constructor at all ([class.default.ctor]/1), so the loop below finds
    // no default constructor to reject: track whether one exists.
    bool has_default_ctor = false, has_any_ctor = false;
    for(const auto &comp : st.components())
    {
      if(comp.get_bool(ID_is_static) || comp.get_bool(ID_is_type))
        continue;
      if(comp.get_bool(ID_is_vtptr))
        return false; // a polymorphic class
      if(comp.type().id() == ID_code)
      {
        const code_typet &code_type = to_code_type(comp.type());
        if(comp.get_bool(ID_is_virtual))
          return false;
        const irep_idt &return_id = code_type.return_type().id();
        // parameters: `this' and the rest
        const std::size_t n_args = code_type.parameters().size();
        if(return_id == ID_destructor)
        {
          if(!code_type.get_bool("#is_implicit_dtor"))
            return false;
        }
        else if(return_id == ID_constructor)
        {
          if(!comp.get_bool(ID_from_base))
          {
            has_any_ctor = true;
            if(n_args == 1)
              has_default_ctor = true;
          }
          // a copy or move constructor: one parameter of reference to the
          // class; user-provided -> not trivial
          const bool copy_or_move =
            n_args == 2 && is_reference(code_type.parameters()[1].type()) &&
            to_reference_type(code_type.parameters()[1].type())
                .base_type()
                .id() == ID_struct_tag &&
            to_struct_tag_type(
              to_reference_type(code_type.parameters()[1].type()).base_type())
                .get_identifier() == to_struct_tag_type(type).get_identifier();
          if(copy_or_move && !code_type.get_bool("#is_implicit_ctor"))
            return false;
          // [class.default.ctor]/3: a trivial class has no user-provided
          // default constructor
          if(
            want_trivial && n_args == 1 &&
            !code_type.get_bool("#is_implicit_ctor"))
            return false;
        }
        else if(comp.get_base_name() == "operator=")
        {
          if(n_args == 2 && !code_type.get_bool("#is_implicit_assign"))
            return false;
        }
        continue;
      }
      // [class.default.ctor]/3: a default member initializer makes the
      // default constructor non-trivial
      if(want_trivial && comp.find(ID_C_default_value).is_not_nil())
        return false;
      if(!is_trivially_copyable_type(comp.type(), want_trivial, depth - 1))
        return false;
    }
    // (a class without any constructor component -- a POD the front end
    // synthesizes no special members for -- has the implicit one)
    return !want_trivial || has_default_ctor || !has_any_ctor;
  }
  if(type.id() == ID_union_tag)
  {
    const union_typet &ut = follow_tag(to_union_tag_type(type));
    for(const auto &comp : ut.components())
    {
      if(
        comp.get_bool(ID_is_static) || comp.get_bool(ID_is_type) ||
        comp.type().id() == ID_code)
        continue;
      if(!is_trivially_copyable_type(comp.type(), want_trivial, depth - 1))
        return false;
    }
    return true;
  }
  // [class.bit]/1: a bit-field member has the (scalar) type of its
  // declaration; the width does not affect triviality
  if(type.id() == ID_c_bit_field)
  {
    return is_trivially_copyable_type(
      to_c_bit_field_type(type).underlying_type(), want_trivial, depth - 1);
  }
  // scalars ([basic.types.general]/9); a reference is not an object type
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
         type.id() == ID_c_bool || type.id() == ID_bool ||
         type.id() == ID_floatbv || type.id() == ID_fixedbv ||
         type.id() == ID_c_enum_tag || type.id() == ID_c_enum ||
         (type.id() == ID_pointer && !is_reference(type));
}

/// N5008 [except.spec]/8: an implicitly-declared default constructor, or one
/// defaulted on its first declaration, is non-throwing unless the
/// initialization of a subobject (a base or member default-initialized by
/// it) is potentially-throwing; a user-provided one is non-throwing only when
/// declared so ([except.spec]/2, `noexcept').  Default member initializers
/// are taken to be non-throwing (their expressions are not type-checked
/// here).
bool cpp_typecheckt::default_construction_is_nothrow(
  const typet &type,
  int depth)
{
  if(depth <= 0)
    return false;
  if(type.id() == ID_array)
  {
    return default_construction_is_nothrow(
      to_array_type(type).element_type(), depth - 1);
  }
  if(type.id() != ID_struct_tag)
    return true; // scalars, unions of trivial members, pointers
  elaborate_class_template(type);
  const struct_typet &st = follow_tag(to_struct_tag_type(type));
  const struct_typet::componentt *ctor = nullptr;
  for(const auto &c : st.components())
  {
    if(c.type().id() != ID_code || c.get_bool(ID_from_base))
      continue;
    const code_typet &ct = to_code_type(c.type());
    if(ct.return_type().id() == ID_constructor && ct.parameters().size() == 1)
    {
      ctor = &c;
      break;
    }
  }
  if(ctor != nullptr)
  {
    const code_typet &ct = to_code_type(ctor->type());
    if(ct.get_bool("#C_noexcept") || ct.get_bool(ID_noexcept))
      return true;
    const symbolt *ctor_symbol = symbol_table.lookup(ctor->get_name());
    const bool implicit_or_defaulted =
      ct.get_bool("#is_implicit_ctor") ||
      (ctor_symbol != nullptr &&
       ctor_symbol->value.get_bool("#defaulted_function"));
    if(!implicit_or_defaulted)
      return false;
  }
  for(const auto &base : st.bases())
  {
    if(!default_construction_is_nothrow(base.type(), depth - 1))
      return false;
  }
  for(const auto &c : st.components())
  {
    if(
      c.type().id() == ID_code || c.get_bool(ID_is_static) ||
      c.get_bool(ID_is_type) || c.get_bool(ID_from_base) ||
      c.get_bool(ID_is_vtptr) || c.get_is_padding())
    {
      continue;
    }
    if(c.find(ID_C_default_value).is_not_nil())
      continue; // initialized from its default member initializer
    if(!default_construction_is_nothrow(c.type(), depth - 1))
      return false;
  }
  return true;
}

bool cpp_typecheckt::compound_requirement_is_satisfied(const exprt &expr)
{
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  bool satisfied = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    exprt op = to_unary_expr(expr).op();
    // see requirement_expression_is_valid: empty packs must be expanded
    expand_requires_parameter_packs(op);
    template_map.expand_call_argument_packs(op);
    {
      // [expr.prim.req.general]/2: the expression is an unevaluated operand
      unevaluated_operandt unevaluated_guard{*this};
      typecheck_expr(op);
    }

    const irept &constraint = expr.find("#constraint");
    if(constraint.is_not_nil())
    {
      // [expr.prim.req.compound]/1: the return-type-requirement names a
      // type-constraint C; the requirement is satisfied only if
      // C<decltype((E))> is satisfied.  decltype((E)) uses the
      // parenthesised form ([dcl.type.decltype]/1.4-1.6): an lvalue E
      // yields T&, an xvalue T&&, a prvalue T -- the same rule decltype
      // itself applies.  A call returning an rvalue reference
      // (ranges::iter_move(i) -> int&&) is an xvalue; taking the
      // implicitly dereferenced operand's type made it `int', and
      // `-> same_as<iter_rvalue_reference_t<_In>>' failed, so no pointer
      // was indirectly_readable under libc++.
      const typet result_type = decltype_of(op, true);

      irep_idt concept_name;
      const irept *constraint_args = nullptr;
      for(const auto &sub : constraint.get_sub())
      {
        if(sub.id() == ID_name)
          concept_name = sub.get(ID_identifier);
        else if(sub.id() == ID_template_args)
          constraint_args = &sub;
      }

      // N5008 [expr.prim.req.compound]/1: the requirement is satisfied
      // exactly when C<decltype((E))> is satisfied.  Evaluate that
      // CONCEPT-ID -- the form a user writes -- so it goes through the
      // normal concept-instantiation path.  The manual substitution
      // below cannot work in general: the stored concept body keeps its
      // template argument as an `ambiguous` node with an EMPTY type, so
      // neither template_mapt::apply nor a by-name walk can replace the
      // parameter, and the verdict then depended on ambient scope state
      // (a satisfied requirement read as unsatisfied for every
      // trait-based concept, e.g. libc++'s __has_integral_minus).
      if(!concept_name.empty())
      {
        cpp_namet concept_id;
        concept_id.get_sub().push_back(irept(ID_name));
        concept_id.get_sub().back().set(ID_identifier, concept_name);
        irept targs(ID_template_args);
        irept &args_sub = targs.add(ID_arguments);
        exprt first_arg{ID_type};
        first_arg.type() = result_type;
        args_sub.get_sub().push_back(first_arg);
        bool args_ok = true;
        if(constraint_args != nullptr)
        {
          for(const auto &a : constraint_args->find(ID_arguments).get_sub())
          {
            const exprt &ae = static_cast<const exprt &>(a);
            typet arg_type = ae.type();
            // An explicit type-constraint argument (`same_as_<_Tp>`)
            // is left by the parser as an `ambiguous` node whose type
            // is an unresolved cpp_name.  Here the CURRENT SCOPE is the
            // root, so name lookup cannot resolve it -- but the
            // enclosing template's binding is in the template map;
            // use it ([temp.names]/1, [temp.arg]/1).
            if(arg_type.id() == ID_cpp_name)
            {
              irep_idt short_name;
              for(const auto &ns : arg_type.get_sub())
                if(ns.id() == ID_name)
                  short_name = ns.get(ID_identifier);
              bool resolved = false;
              if(!short_name.empty())
              {
                for(const auto &te : template_map.type_map)
                {
                  const std::string key = id2string(te.first);
                  const auto pos = key.rfind("::");
                  const std::string suffix =
                    pos != std::string::npos ? key.substr(pos + 2) : key;
                  if(
                    suffix == id2string(short_name) &&
                    te.second.id() != ID_unassigned && te.second.is_not_nil())
                  {
                    arg_type = te.second;
                    resolved = true;
                    break;
                  }
                }
              }
              if(!resolved)
              {
                try
                {
                  typecheck_type(arg_type);
                  resolved = arg_type.id() != ID_cpp_name;
                }
                catch(...)
                {
                  resolved = false;
                }
              }
              if(!resolved)
              {
                args_ok = false;
                break;
              }
            }
            else if(arg_type.is_not_nil() && !arg_type.id().empty())
            {
              // A compound type naming the parameter -- `same_as<T &>` in
              // `{ ++a } -> same_as<T &>` -- is substituted through the
              // enclosing template's map and type-checked NOW, while that
              // map is live (the concept-id below is evaluated with an
              // empty map).  Left as written, `T &` reached the concept
              // unresolved and the requirement read as unsatisfied.
              try
              {
                template_map.apply(arg_type);
                typecheck_type(arg_type);
              }
              catch(...)
              {
                args_ok = false;
                break;
              }
            }
            exprt as_type{ID_type};
            as_type.type() = arg_type;
            args_sub.get_sub().push_back(as_type);
          }
        }
        if(args_ok)
        {
          concept_id.get_sub().push_back(targs);
          exprt as_expr = concept_id.as_expr();
          as_expr.add_source_location() = expr.source_location();
          bool decided = false;
          try
          {
            // The synthetic concept-id carries CONCRETE arguments, so no
            // enclosing bindings are needed to evaluate it -- and they
            // must not be visible: the concept's own parameters
            // typically share their short names with the enclosing
            // template's (`_Tp`/`_Up`), and the resolver's short-name
            // bridge would then substitute the ENCLOSING binding for
            // them, making `same_as_<int, weird>` evaluate as
            // `same_as_<weird, weird>` (V1 in
            // doc/architectural/cpp-frontend-review-2026-06-24-
            // template-map-scope.md).  Evaluate with an empty map.
            cpp_saved_template_mapt saved_concept_map{template_map};
            template_map.clear();
            typecheck_expr(as_expr);
            simplify(as_expr, *this);
            // [temp.constr.atomic]/1: contextually converted to bool.
            // A `bool`-typed constant is not recognised by is_zero(),
            // so test the boolean forms first (the same trap that made
            // the legacy path read every satisfied requirement as
            // unsatisfied).
            if(as_expr.is_true())
            {
              satisfied = true;
              decided = true;
            }
            else if(as_expr.is_false())
            {
              satisfied = false;
              decided = true;
            }
            else if(as_expr.is_constant())
            {
              satisfied = !to_constant_expr(as_expr).is_zero();
              decided = true;
            }
          }
          catch(...)
          {
            // undecidable here: fall through to the legacy path
          }
          if(decided)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            return satisfied;
          }
        }
      }

      if(!concept_name.empty())
      {
        const auto cids = cpp_scopes.current_scope().lookup(
          concept_name, cpp_scopet::RECURSIVE);
        bool evaluated = false;
        for(const auto *cid : cids)
        {
          const auto *csym = symbol_table.lookup(cid->identifier);
          if(!csym || !csym->type.get_bool(ID_is_template))
            continue;
          const auto &cd = to_cpp_declaration(csym->type);
          if(cd.declarators().empty())
            continue;
          exprt cbody = cd.declarators()[0].value();
          if(cbody.is_nil())
            continue;
          // Build C's argument list: decltype((E)) prepended to the explicit
          // type-constraint arguments ([temp.names]/9,
          // [expr.prim.req.compound]).
          cpp_template_args_tct check_args;
          exprt prepended{ID_type};
          prepended.type() = result_type;
          check_args.arguments().push_back(std::move(prepended));
          if(constraint_args != nullptr)
          {
            const irept &args_sub = constraint_args->find(ID_arguments);
            for(const auto &a : args_sub.get_sub())
            {
              exprt arg_copy = static_cast<const exprt &>(a);
              typecheck_type(arg_copy.type());
              check_args.arguments().push_back(std::move(arg_copy));
            }
          }
          template_mapt cmap;
          cmap.build(cd.template_type(), check_args);
          cmap.apply(cbody);
          // N5008 [temp.constr.op] + [expr.prim.req.compound]/1: the
          // concept body may be a CONJUNCTION/DISJUNCTION of type
          // predicates whose operand types live in the
          // `type_arg`/`type_arg1`/`type_arg2` NAMED sub-nodes
          // (libc++ same_as = `__is_same(_Tp,_Up) && __is_same(_Up,_Tp)`).
          // template_mapt::apply(exprt) does not descend into those
          // named sub-nodes of NESTED children (its unnamed-children
          // recursion goes through the typet overload, which does not
          // know predicate nodes), so the substituted body kept the
          // bare parameter names, failed to typecheck, and the
          // requirement evaluated FALSE.  Substitute them with a local
          // walk over the (small) body -- children first, so a bound
          // value's own subtree is not re-walked.
          {
            std::function<void(irept &)> apply_pred_args = [&](irept &n)
            {
              for(auto &c : n.get_sub())
                apply_pred_args(c);
              for(const auto &key :
                  {ID_type_arg, irep_idt{"type_arg1"}, irep_idt{"type_arg2"}})
              {
                if(n.find(key).is_not_nil())
                  cmap.apply(static_cast<typet &>(n.add(key)));
              }
            };
            apply_pred_args(cbody);
          }
          // Evaluate C's body recursively through typecheck_expr so nested
          // requirements / concept-ids resolve via the same machinery.
          typecheck_expr(cbody);
          simplify(cbody, *this);
          if(!cbody.is_true())
            satisfied = false;
          evaluated = true;
          break;
        }
        // If the named concept could not be resolved at all, fall back to the
        // validity of E (already established above): do not spuriously fail.
        (void)evaluated;
      }
    }
  }
  catch(...)
  {
    satisfied = false;
  }
  if(
    get_message_handler().get_message_count(messaget::M_ERROR) != errors_before)
    satisfied = false;
  get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  return satisfied;
}

/// Called after the operands are done
void cpp_typecheckt::typecheck_expr_main(exprt &expr)
{
  // N5008 [expr.prim.fold]/1: an expanded fold over an assignment operator
  // (see Parser::rExpression) arrives as a two-operand node whose id is the
  // assignment's statement; it is that assignment
  {
    static const std::set<irep_idt> assignments{
      ID_assign,
      ID_assign_plus,
      ID_assign_minus,
      ID_assign_mult,
      ID_assign_div,
      ID_assign_mod,
      ID_assign_shl,
      ID_assign_shr,
      ID_assign_bitand,
      ID_assign_bitxor,
      ID_assign_bitor};
    if(expr.operands().size() == 2 && assignments.count(expr.id()) != 0)
    {
      exprt assignment{ID_side_effect};
      assignment.set(ID_statement, expr.id());
      assignment.operands() = std::move(expr.operands());
      assignment.add_source_location() = expr.source_location();
      expr.swap(assignment);
    }
  }

  if(expr.id() == ID_cpp_name)
    typecheck_expr_cpp_name(expr, cpp_typecheck_fargst());
  else if(
    (expr.id() == ID_struct || expr.id() == ID_array) &&
    expr.type().id() != ID_nil && !expr.type().id().empty())
  {
    // A CONSTANT of class or array type -- the folded value of a constexpr
    // object substituted for its symbol, e.g. `constexpr Fixed f{42}` as
    // the argument of a class-type non-type template parameter (N5008
    // [temp.param]/7, [temp.arg.nontype]/1); it is already type-checked and
    // has nothing to resolve.  (The C front-end's handler treats a struct
    // or array node as unexpected.)
  }
  else if(expr.id() == ID_string_constant)
  {
    // N5008 [lex.string]/6: an ordinary string literal has type "array of n
    // const char" (the C front-end types it `char[n]', C's rule).  The
    // constness matters for overload resolution: `std::string s("...")`
    // must select the non-template `basic_string(const char *)` -- with
    // a `char[n]' argument that candidate needs a qualification
    // conversion on top of the array-to-pointer conversion, and the
    // string_view constructor template `basic_string(const _Tp &)`
    // (deducing `_Tp = char[n]`, an identity binding) won instead,
    // returning the wrong length.
    c_typecheck_baset::typecheck_expr_main(expr);
    if(expr.type().id() == ID_array)
      to_array_type(expr.type()).element_type().set(ID_C_constant, true);
  }
  else if(expr.id() == "cpp-this")
    typecheck_expr_this(expr);
  else if(expr.id() == ID_pointer_to_member)
    convert_pmop(expr);
  else if(expr.id() == ID_new_object)
  {
  }
  else if(
    (expr.id() == ID_and || expr.id() == ID_or) && expr.operands().size() > 2)
  {
    // An n-ary conjunction/disjunction: the satisfaction of a
    // requires-expression is built as one `and' over all its requirements
    // ([expr.prim.req.general]/5) and reaches this point when the
    // enclosing `if constexpr' condition is checked.  The C front end's
    // handler is for the binary source form and asserts two operands;
    // and_exprt/or_exprt are n-ary, so convert each operand to bool.
    for(auto &op : expr.operands())
      implicit_typecast_bool(op);
    expr.type() = bool_typet();
  }
  else if(operator_is_overloaded(expr))
  {
  }
  else if(expr.id() == ID_spaceship && expr.operands().size() == 2)
  {
    // N5008 [expr.spaceship]/7-8: the built-in three-way comparison of two
    // operands of arithmetic type yields a value of a comparison category
    // type, NOT an int -- std::strong_ordering for integral operands and
    // std::partial_ordering for floating-point operands.  (The plain int
    // lowering in the C front-end is wrong for C++: `std::strong_ordering r =
    // a <=> b;` then fails with "invalid implicit conversion from int".)  We
    // lower to a conditional selecting the library's comparison-category
    // constants, which is what the result is specified to equal.  When the
    // <compare> header (hence the category type) is not available we fall back
    // to the C int lowering, preserving the existing lenient behaviour.
    const exprt &op0 = to_binary_expr(expr).op0();
    const exprt &op1 = to_binary_expr(expr).op1();
    const typet &t0 = op0.type();
    const typet &t1 = op1.type();

    auto is_arith = [](const typet &t)
    {
      return t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
             t.id() == ID_floatbv || t.id() == ID_fixedbv ||
             t.id() == ID_bool || t.id() == ID_c_bool ||
             t.id() == ID_c_enum_tag || t.id() == ID_c_enum;
    };
    const bool is_fp = t0.id() == ID_floatbv || t1.id() == ID_floatbv ||
                       t0.id() == ID_fixedbv || t1.id() == ID_fixedbv;

    // Resolve std::<category>::<member> to its (static const) object, quietly.
    auto resolve_category_member =
      [&](const char *category, const char *member) -> exprt
    {
      exprt name{ID_cpp_name};
      auto &sub = name.get_sub();
      sub.push_back(irept{ID_name});
      sub.back().set(ID_identifier, "std");
      sub.push_back(irept{ID_scope_resolution});
      sub.push_back(irept{ID_name});
      sub.back().set(ID_identifier, category);
      sub.push_back(irept{ID_scope_resolution});
      sub.push_back(irept{ID_name});
      sub.back().set(ID_identifier, member);
      name.add_source_location() = expr.source_location();

      const std::size_t saved_errors =
        get_message_handler().get_message_count(messaget::M_ERROR);
      const unsigned saved_verbosity = get_message_handler().get_verbosity();
      get_message_handler().set_verbosity(0);
      exprt resolved = name;
      try
      {
        cpp_save_scopet save_scope(cpp_scopes);
        typecheck_expr(resolved);
      }
      catch(...)
      {
        resolved.make_nil();
      }
      get_message_handler().set_message_count(messaget::M_ERROR, saved_errors);
      get_message_handler().set_verbosity(saved_verbosity);
      return resolved;
    };

    // [expr.spaceship]/8: two operands of pointer type (after the composite
    // pointer type conversion) also yield std::strong_ordering.  Only the
    // arithmetic case was lowered; `p <=> q' fell to the C int lowering, and
    // `if(const auto cmp = x <=> y; cmp != 0) return cmp;' in a function
    // returning strong_ordering (libstdc++ 16's _Bit_iterator_base) failed.
    const bool is_ptr = t0.id() == ID_pointer && t1.id() == ID_pointer &&
                        !is_reference(t0) && !is_reference(t1);

    bool lowered = false;
    if((is_arith(t0) && is_arith(t1)) || is_ptr)
    {
      const char *category = is_fp ? "partial_ordering" : "strong_ordering";
      exprt less = resolve_category_member(category, "less");
      exprt greater = resolve_category_member(category, "greater");
      exprt equalish =
        resolve_category_member(category, is_fp ? "equivalent" : "equal");
      exprt unordered =
        is_fp ? resolve_category_member(category, "unordered") : nil_exprt();

      if(
        less.is_not_nil() && greater.is_not_nil() && equalish.is_not_nil() &&
        (!is_fp || unordered.is_not_nil()))
      {
        // N5008 [expr.spaceship]/2, /4.2, /6: `p <=> q' is a PRVALUE of type
        // std::strong_ordering (resp. partial_ordering) -- not of the type
        // of the `static constexpr' member it yields, which is const: a
        // `const strong_ordering' made libc++'s
        // __compares_as<decltype((a <=> b)), partial_ordering> evaluate
        // __type_to_enum<const strong_ordering>() as _None, so
        // three_way_comparable_with<T *, T *> was false and
        // std::compare_three_way()(p, q) had no viable operator().
        typet cat_type = less.type();
        cat_type.remove(ID_C_constant);
        cat_type.remove(ID_C_volatile);
        const source_locationt loc = expr.source_location();

        // [expr.spaceship]/4: the usual arithmetic conversions are applied
        // to arithmetic operands (so a comparison result, of the internal
        // `bool' type, and a `true' of C++ bool type compare in a common
        // type; `(a == b) <=> true' -- libstdc++'s
        // lexicographical_compare_three_way -- evaluated wrongly otherwise)
        exprt a = op0, b = op1;
        if(!is_ptr)
          implicit_typecast_arithmetic(a, b);

        binary_relation_exprt lt{a, ID_lt, b};
        lt.type() = bool_typet();
        lt.add_source_location() = loc;
        binary_relation_exprt gt{a, ID_gt, b};
        gt.type() = bool_typet();
        gt.add_source_location() = loc;

        if(is_ptr)
        {
          // N5008 [expr.spaceship]/6: p <=> q yields equal if p and q compare
          // equal ([expr.eq]); otherwise less if q compares greater than p,
          // else greater.  Equality is decided first: for pointers to
          // different complete objects the order is unspecified
          // ([expr.rel]/4 -- cbmc's `<' / `>' are then unconstrained), but
          // the pointers never compare equal, so the result is never equal.
          binary_relation_exprt eq{a, ID_equal, b};
          eq.type() = bool_typet();
          eq.add_source_location() = loc;
          if_exprt inner{lt, less, greater, cat_type};
          if_exprt outer{eq, equalish, inner, cat_type};
          outer.add_source_location() = loc;
          expr.swap(outer);
        }
        else if(!is_fp)
        {
          // a < b ? less : (a > b ? greater : equal)
          if_exprt inner{gt, greater, equalish, cat_type};
          if_exprt outer{lt, less, inner, cat_type};
          outer.add_source_location() = loc;
          expr.swap(outer);
        }
        else
        {
          // a < b ? less : (a > b ? greater : (a == b ? equivalent :
          // unordered))
          binary_relation_exprt eq{a, ID_equal, b};
          eq.type() = bool_typet();
          eq.add_source_location() = loc;
          if_exprt i3{eq, equalish, unordered, cat_type};
          if_exprt i2{gt, greater, i3, cat_type};
          if_exprt outer{lt, less, i2, cat_type};
          outer.add_source_location() = loc;
          expr.swap(outer);
        }
        lowered = true;
      }
    }

    if(!lowered)
      c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id() == "explicit-typecast")
    typecheck_expr_explicit_typecast(expr);
  else if(expr.id() == ID_typecast && expr.type().id() == ID_cpp_name)
  {
    typecheck_type(expr.type());
    c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id() == "type_requirement")
  {
    // N5008 [expr.prim.req.type]/1 + [expr.prim.req.general]/5: the
    // requirement is satisfied iff the named type is valid; a substitution
    // failure in the immediate context (`typename T::value_type` with T =
    // int) makes the requires-expression false, it is not ill-formed.  A
    // thrown failure used to escape to the constraint evaluation, which
    // took the unevaluated constraint as satisfied and selected the
    // constrained partial specialization for int.
    typet &t = static_cast<typet &>(expr.add(ID_type_arg));
    const std::size_t errors_before =
      get_message_handler().get_message_count(messaget::M_ERROR);
    bool valid = true;
    try
    {
      sfinae_contextt sfinae_guard{*this};
      template_map.apply(t);
      typecheck_type(t);
    }
    catch(...)
    {
      valid = false;
    }
    if(
      get_message_handler().get_message_count(messaget::M_ERROR) !=
      errors_before)
    {
      valid = false;
      get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
    }
    expr = typecast_exprt{
      valid ? static_cast<exprt>(true_exprt())
            : static_cast<exprt>(false_exprt()),
      c_bool_type()};
  }
  else if(expr.id() == "simple_requirement")
  {
    // [expr.prim.req.simple]/1: a simple-requirement is satisfied iff the
    // expression is valid.  [expr.prim.req.general]/5: an invalid expression
    // in the immediate context makes the requires-expression evaluate to
    // false, not ill-formed.  requirement_expression_is_valid converts any
    // failure (including errors that do not throw, e.g. member access on a
    // non-class type) into a soft `false`.
    bool satisfied;
    if(expr.operands().size() == 1)
      satisfied = requirement_expression_is_valid(to_unary_expr(expr).op());
    else
      // Defensive: a malformed/empty requirement node (can arise from a
      // requirement form the parser did not fully model, seen in the deep
      // <ranges> concept chain).  Do not abort on it (to_unary_expr would
      // trip an invariant); treat the unmodelled requirement as satisfied so
      // it neither crashes nor spuriously fails the concept.
      satisfied = true;
    expr = typecast_exprt{
      satisfied ? static_cast<exprt>(true_exprt())
                : static_cast<exprt>(false_exprt()),
      c_bool_type()};
  }
  else if(expr.id() == "compound_requirement")
  {
    // [expr.prim.req.compound]/1: { E } -> C is satisfied iff E is a valid
    // expression and, when the return-type-requirement C is present,
    // C<decltype((E))> is satisfied.  Substitution failure in the immediate
    // context is a soft failure ([expr.prim.req.general]/5).
    bool satisfied;
    if(expr.operands().size() == 1)
      satisfied = compound_requirement_is_satisfied(expr);
    else
      satisfied = true; // defensive: see simple_requirement above
    expr = typecast_exprt{
      satisfied ? static_cast<exprt>(true_exprt())
                : static_cast<exprt>(false_exprt()),
      c_bool_type()};
  }
  else if(expr.id() == "concept_check")
  {
    // C++20 nested concept requirement: requires ConceptName<T>;
    // Look up the concept and evaluate its body.
    const irep_idt &concept_name = expr.get("concept_name");
    const auto concept_ids =
      cpp_scopes.current_scope().lookup(concept_name, cpp_scopet::RECURSIVE);
    if(concept_ids.empty())
      throw 0;
    const auto *concept_sym =
      symbol_table.lookup((*concept_ids.begin())->identifier);
    if(!concept_sym || !concept_sym->type.get_bool(ID_is_template))
      throw 0;
    const cpp_declarationt &concept_decl =
      to_cpp_declaration(concept_sym->type);
    if(concept_decl.declarators().empty())
      throw 0;
    exprt body = concept_decl.declarators()[0].value();
    if(body.is_nil())
      throw 0;
    // Apply the current template_map to substitute parameters
    template_map.apply(body);
    typecheck_expr(body);
    simplify(body, *this);
    if(body.is_false())
      throw 0;
    expr = typecast_exprt{true_exprt(), c_bool_type()};
  }
  else if(expr.id() == ID_bit_cast)
  {
    // __builtin_bit_cast(Type, expr) — resolve cpp_name type
    if(expr.type().id() == ID_cpp_name)
      typecheck_type(expr.type());
    c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id() == "explicit-constructor-call")
    typecheck_expr_explicit_constructor_call(expr);
  else if(expr.id() == ID_code)
  {
    // The parser may produce ID_code for expressions like bool(x)
    // when it cannot distinguish a functional cast from a function type.
    // Check if this looks like a functional cast: return type is a
    // primitive type and there is exactly one parameter.
    const irept &return_type = expr.find(ID_return_type);
    const irept &parameters = expr.find(ID_parameters);
    if(
      return_type.is_not_nil() && parameters.get_sub().size() == 1 &&
      parameters.get_sub()[0].id() == ID_cpp_declaration)
    {
      typet cast_target = static_cast<const typet &>(return_type);
      typecheck_type(cast_target);

      // Extract the parameter declaration's type as an expression
      const auto &param_decl =
        static_cast<const cpp_declarationt &>(parameters.get_sub()[0]);
      exprt cast_arg = static_cast<const exprt &>(
        static_cast<const irept &>(param_decl.type()));
      typecheck_expr(cast_arg);
      expr = typecast_exprt(cast_arg, cast_target);
      return;
    }
    // A return statement in expression context can occur when a
    // constexpr function body is used as a value during template
    // instantiation.  Extract the return value.
    if(expr.get(ID_statement) == ID_return && expr.operands().size() == 1)
    {
      exprt ret_val = to_code_frontend_return(to_code(expr)).return_value();
      typecheck_expr(ret_val);
      expr = ret_val;
      return;
    }
    error().source_location = expr.source_location();
    error() << "unexpected ID_code expression" << eom;
    throw 0;
  }
  else if(expr.id() == ID_compound_literal && expr.type().is_not_nil())
  {
    // Produced by the explicit-typecast forms (`T{}', `T()' for a class,
    // `(T){...}') from an already type-checked operand; reaching here means
    // the expression is type-checked a second time -- as an element of a
    // braced-init-list argument is when the call's arguments are converted
    // (`test<S>({S{}})').  Nothing to do ("unexpected expression:
    // compound_literal" otherwise).
  }
  else if(expr.id() == ID_symbol)
  {
    // A symbol expression is normally already resolved.  The one exception
    // is a TYPELESS reference to a CPROVER primitive in the synthesized body
    // of a GCC polymorphic builtin (`__CPROVER_atomic_begin' in
    // __atomic_fetch_add's implementation, c_typecheck_gcc_polymorphic_
    // builtins.cpp): the C front end resolves it in typecheck_expr_symbol,
    // this one left it typeless, and the call then failed ("function call
    // expects function or function pointer as argument") -- so every
    // __atomic_* / __sync_* builtin was unusable in C++, and with it
    // libstdc++'s __gnu_cxx::__atomic_add (shared_ptr, locale).
    const irep_idt &identifier = to_symbol_expr(expr).get_identifier();
    if(expr.type().is_nil() || expr.type().id().empty())
    {
      // a CPROVER primitive is declared on first use (builtin_factory), as
      // the C front end does on a failed lookup
      if(!symbol_table.has_symbol(identifier))
        builtin_factory(identifier);
      const symbolt *symbol = symbol_table.lookup(identifier);
      if(symbol != nullptr && !symbol->is_type)
        expr.type() = symbol->type;
    }
    // The same synthesized bodies name their C-mode locals (`result') by a
    // typed symbol expression without the lvalue mark the C front end's
    // typecheck_expr_symbol would add (`&result' then failed: "not an
    // lvalue").  C++ symbols are resolved -- and marked -- by the resolver;
    // C-mode ones are not, so mark those here.
    if(!expr.get_bool(ID_C_lvalue))
    {
      const symbolt *symbol = symbol_table.lookup(identifier);
      if(
        symbol != nullptr && symbol->mode == ID_C && symbol->is_lvalue &&
        !symbol->is_type && !symbol->is_macro)
      {
        expr.set(ID_C_lvalue, true);
      }
    }
  }
  else if(expr.id() == "__is_base_of")
  {
    // an MS extension, also a Clang/GCC built-in.  Per N5008
    // [meta.rel] table: `is_base_of<Base, Derived>::value` is
    // true iff `Base` is a base class of `Derived` (or the same
    // class).  Both `class` and `struct` declarations produce
    // class types per [class]/1; CBMC stores `struct` as a
    // `struct_typet` without `ID_C_class`, while `class` sets
    // `ID_C_class`.  `to_class_type` requires `ID_C_class`, so
    // call `to_struct_type` here — a struct is a class-key for
    // base-class purposes regardless of the `class`/`struct`
    // keyword.

    typet base = static_cast<const typet &>(expr.find("type_arg1"));
    typet deriv = static_cast<const typet &>(expr.find("type_arg2"));

    typecheck_type(base);
    typecheck_type(deriv);

    if(base.id() != ID_struct_tag || deriv.id() != ID_struct_tag)
      expr = false_exprt();
    else
    {
      // N5008 [meta.rel]: Derived shall be a complete type when it is a
      // non-union class type different from Base -- complete it (a class
      // template specialization named here for the first time,
      // `iterator_traits<int*>` in libstdc++'s __primary_traits_iter).
      // Comparing the two classes by their (empty, for an incomplete
      // class) ID_name made every pair of incomplete classes "the same
      // class", so the concept held for every pointer.
      const irep_idt base_id = to_struct_tag_type(base).get_identifier();
      const irep_idt deriv_id = to_struct_tag_type(deriv).get_identifier();
      if(base_id != deriv_id)
      {
        struct_tag_typet deriv_tag = to_struct_tag_type(deriv);
        deriv_tag.add_source_location() = expr.source_location();
        try
        {
          elaborate_class_template(deriv_tag);
        }
        catch(...)
        {
        }
      }
      const struct_typet &struct_type = follow_tag(to_struct_tag_type(deriv));

      // Per N5008 [meta.rel] / Cpp17BaseOfRequirement: a type is
      // a base of itself for the purposes of `is_base_of`, and a base
      // class may be INDIRECT ([class.derived.general]/2:
      // random_access_iterator_tag -> bidirectional -> forward -> input;
      // has_base() sees direct bases only, so derived_from<random_access_
      // iterator_tag, input_iterator_tag> was false and no user iterator
      // satisfied std::input_iterator).
      std::set<irep_idt> all_bases;
      std::function<void(const struct_typet &)> collect =
        [&](const struct_typet &t)
      {
        for(const auto &b : t.bases())
        {
          // baset::type() asserts a struct_tag; a base of a class template
          // member not yet elaborated may still be a dependent name
          const typet &base_type = static_cast<const typet &>(b.find(ID_type));
          if(base_type.id() != ID_struct_tag)
            continue;
          const irep_idt bid = to_struct_tag_type(base_type).get_identifier();
          if(!all_bases.insert(bid).second)
            continue;
          const symbolt *bs = symbol_table.lookup(bid);
          if(bs != nullptr && bs->type.id() == ID_struct)
            collect(to_struct_type(bs->type));
        }
      };
      collect(struct_type);
      if(base_id == deriv_id || all_bases.count(base_id) != 0)
        expr = true_exprt();
      else
        expr = false_exprt();
    }
  }
  else if(expr.id() == ID_msc_uuidof)
  {
    // these appear to have type "struct _GUID"
    // and they are lvalues!
    expr.type() = struct_tag_typet("tag-_GUID");
    expr.set(ID_C_lvalue, true);
  }
  else if(expr.id() == ID_typeid)
    typecheck_expr_typeid(expr);
  else if(
    expr.id() == "__is_invocable" || expr.id() == "__is_nothrow_invocable")
  {
    typecheck_expr_is_invocable(expr);
  }
  else if(expr.id() == "__array_rank")
  {
    // N5008 [meta.unary.prop.query]: rank<T> is the number of array
    // dimensions of T (GCC 14's builtin, libstdc++ 16's std::rank).
    typet t = static_cast<const typet &>(expr.find(ID_type_arg));
    typecheck_type(t);
    std::size_t rank = 0;
    while(t.id() == ID_array)
    {
      ++rank;
      t = to_array_type(t).element_type();
    }
    expr = from_integer(rank, size_type());
  }
  else if(
    expr.id() == "__is_constructible" || expr.id() == "__is_assignable" ||
    expr.id() == "__is_convertible_to" || expr.id() == "__is_convertible" ||
    expr.id() == "__is_trivially_constructible" ||
    expr.id() == "__is_trivially_assignable" ||
    expr.id() == "__is_nothrow_constructible" ||
    expr.id() == "__is_nothrow_assignable" || expr.id() == "__is_same" ||
    expr.id() == "__is_layout_compatible" ||
    expr.id() == "__is_nothrow_convertible" ||
    expr.id() == "__is_pointer_interconvertible_base_of" ||
    expr.id() == "__reference_constructs_from_temporary" ||
    expr.id() == "__reference_converts_from_temporary" ||
    expr.id() == "__reference_binds_to_temporary")
  {
    // GCC/Clang built-in type traits
    typet t1 = static_cast<const typet &>(expr.find("type_arg1"));
    typet t2 = static_cast<const typet &>(expr.find("type_arg2"));
    if(t1.is_nil() && !expr.find(ID_type_arg).is_nil())
      t1 = static_cast<const typet &>(expr.find(ID_type_arg));
    typecheck_type(t1);
    if(t2.is_not_nil())
    {
      try
      {
        typecheck_type(t2);
      }
      catch(int)
      {
        t2 = typet{ID_nil};
      }
    }

    if(expr.id() == "__is_same")
    {
      // N5008 [meta.rel]/2: is_same<T, U> is true iff T and U denote the same
      // type, INCLUDING cv-qualifiers at every level.  irept::operator==
      // compares the type structure but ignores the cv-qualifier comments
      // (#constant / #volatile / #restricted), so `const int` and `int` would
      // wrongly compare equal.  Require an exact structural match AND matching
      // cv-qualifiers at each level (recursing through single-subtype types
      // such as pointers, references and arrays).
      std::function<bool(const typet &, const typet &)> same_including_cv =
        [&](const typet &a, const typet &b) -> bool
      {
        // [dcl.array]/1: the bound of an array type is a value; the front
        // end's constants for it may differ in their integer type (a
        // string literal's `c_index_type' bound, a declared `size_t' one)
        if(a.id() == ID_array && b.id() == ID_array)
        {
          const auto bound_a =
            numeric_cast<mp_integer>(to_array_type(a).size());
          const auto bound_b =
            numeric_cast<mp_integer>(to_array_type(b).size());
          // [basic.type.qualifier]/3: cv-qualifiers of an array type are
          // those of its elements; the front end records them on either
          if(bound_a.has_value() && bound_b.has_value())
          {
            const auto element = [](const typet &array)
            {
              typet e = to_array_type(array).element_type();
              if(array.get_bool(ID_C_constant))
                e.set(ID_C_constant, true);
              if(array.get_bool(ID_C_volatile))
                e.set(ID_C_volatile, true);
              return e;
            };
            return *bound_a == *bound_b &&
                   same_including_cv(element(a), element(b));
          }
        }
        if(
          a.id() == ID_pointer && b.id() == ID_pointer &&
          to_pointer_type(a).base_type().id() == ID_array &&
          to_pointer_type(b).base_type().id() == ID_array)
        {
          return a.get_bool(ID_C_constant) == b.get_bool(ID_C_constant) &&
                 a.get_bool(ID_C_volatile) == b.get_bool(ID_C_volatile) &&
                 a.get_bool(ID_C_reference) == b.get_bool(ID_C_reference) &&
                 a.get_bool(ID_C_rvalue_reference) ==
                   b.get_bool(ID_C_rvalue_reference) &&
                 same_including_cv(
                   to_pointer_type(a).base_type(),
                   to_pointer_type(b).base_type());
        }
        // [basic.fundamental]: wchar_t and int, char and signed char, long
        // and long long are distinct types (same_fundamental_type_name)
        if(a != b || !same_fundamental_type_name(a, b))
          return false;
        if(
          a.get_bool(ID_C_constant) != b.get_bool(ID_C_constant) ||
          a.get_bool(ID_C_volatile) != b.get_bool(ID_C_volatile) ||
          a.get_bool(ID_C_restricted) != b.get_bool(ID_C_restricted))
          return false;
        // [dcl.ref]: an lvalue reference and an rvalue reference to the same
        // type are different types.  Both are pointer types with the
        // `#reference' comment; the `#rvalue_reference' comment tells them
        // apart, and irept::operator== ignores comments.
        if(
          a.get_bool(ID_C_reference) != b.get_bool(ID_C_reference) ||
          a.get_bool(ID_C_rvalue_reference) !=
            b.get_bool(ID_C_rvalue_reference))
          return false;
        if(a.id() == ID_code)
        {
          // [dcl.fct]/6-7, [basic.type.qualifier]: the parameter types
          // (their nested cv-qualifiers, e.g. `void (*)(const int *)` vs
          // `void (*)(int *)`) and, for a member function type, the
          // cv-qualifier-seq -- modelled as the cv of the implicit object
          // parameter's pointee -- are part of the type's identity.
          const code_typet &ca = to_code_type(a);
          const code_typet &cb = to_code_type(b);
          if(!same_including_cv(ca.return_type(), cb.return_type()))
            return false;
          if(ca.parameters().size() != cb.parameters().size())
            return false;
          for(std::size_t i = 0; i < ca.parameters().size(); ++i)
          {
            if(!same_including_cv(
                 ca.parameters()[i].type(), cb.parameters()[i].type()))
              return false;
          }
          return true;
        }
        if(a.has_subtype())
          return same_including_cv(
            to_type_with_subtype(a).subtype(),
            to_type_with_subtype(b).subtype());
        return true;
      };
      if(same_including_cv(t1, t2))
        expr = true_exprt();
      else
        expr = false_exprt();
    }
    else if(
      expr.id() == "__is_convertible_to" || expr.id() == "__is_convertible")
    {
      // Check if t1 is implicitly convertible to t2.
      if(t1.id() == ID_empty && t2.id() == ID_empty)
      {
        // void -> void is convertible
        expr = true_exprt();
      }
      else if(t1.id() == ID_empty || t2.id() == ID_empty)
      {
        expr = false_exprt();
      }
      else
      {
        exprt tmp;
        // N5008 [meta.rel]/[meta.unary.prop]: the trait is defined via
        // declval<From>(), which is an LVALUE of the underlying type
        // when From is an lvalue reference (reference collapsing,
        // [dcl.ref]/6) and an xvalue otherwise -- in either case the
        // synthesised operand's TYPE is the underlying (non-reference)
        // type; expressions never have reference type
        // ([expr.type]/1).  A reference-typed operand tripped
        // reference_binding's precondition (libc++'s <functional>
        // instantiates __is_convertible with reference types).
        typet from_type = t1;
        if(is_reference(from_type))
          from_type = to_reference_type(from_type).base_type();
        symbol_exprt from(irep_idt(), from_type);
        // [meta.unary.prop], [over.match.copy]/1: the synthesised declval<>()
        // operand is a class prvalue that may need to bind as the implicit
        // object argument of a source-side conversion function; mark it so
        // reference_binding materialises a temporary for that `this` binding.
        from.set(ID_C_temporary_avoided, true);
        if(is_reference(t1) && !is_rvalue_reference(t1))
          from.set(ID_C_lvalue, true);
        if(implicit_conversion_sequence(from, t2, tmp))
          expr = true_exprt();
        else
          expr = false_exprt();
      }
    }
    else if(
      expr.id() == "__is_assignable" ||
      expr.id() == "__is_trivially_assignable" ||
      expr.id() == "__is_nothrow_assignable")
    {
      // __is_assignable(T, U) is true if the expression
      // declval<T>() = declval<U>() is well-formed.
      // For references: T must be an lvalue reference for assignment.
      bool assignable = false;
      if(is_reference(t1))
      {
        typet dest = to_reference_type(t1).base_type();
        // Cannot assign to const
        if(!dest.get_bool(ID_C_constant))
        {
          exprt tmp;
          // See the declval note in __is_convertible above.
          typet from_type = t2;
          if(is_reference(from_type))
            from_type = to_reference_type(from_type).base_type();
          symbol_exprt from(irep_idt(), from_type);
          from.set(ID_C_temporary_avoided, true);
          if(is_reference(t2) && !is_rvalue_reference(t2))
            from.set(ID_C_lvalue, true);
          assignable = implicit_conversion_sequence(from, dest, tmp);
          // N5008 [meta.unary.prop]: `declval<T>() = declval<U>()' is also
          // well-formed through a user-declared `operator=' of the class
          // taking U ([over.match.oper]; `FromInt &operator=(int)'), which
          // the conversion-to-T probe above does not see
          if(!assignable && dest.id() == ID_struct_tag)
          {
            elaborate_class_template(dest);
            for(const auto &c :
                follow_tag(to_struct_tag_type(dest)).components())
            {
              if(c.get_base_name() != "operator=" || c.type().id() != ID_code)
                continue;
              const auto &params = to_code_type(c.type()).parameters();
              if(params.size() != 2)
                continue;
              exprt converted;
              if(implicit_conversion_sequence(
                   from, params[1].type(), converted))
              {
                assignable = true;
                break;
              }
            }
          }
        }
      }
      // else: non-reference T: assignment to an rvalue is not valid for
      // scalar types, but may be valid for class types with operator=.
      // Conservatively false.
      if(expr.id() == "__is_trivially_assignable" && assignable)
      {
        // N5008 [meta.unary.prop]: is_trivially_assignable<T, U> requires
        // additionally that the assignment calls no operation that is not
        // trivial ([class.copy.assign]/9: a trivial copy/move assignment
        // operator is not user-provided, the class has no virtual functions
        // or bases, and every subobject's is trivial).  For a scalar
        // destination the built-in assignment is trivial; for a class
        // destination the class's copy/move assignment must be trivial
        // (is_trivially_copyable_type judges exactly that set of members)
        // and the source must be the same class (anything else selects a
        // user-provided converting assignment or conversion).  This was
        // unconditionally true, like __is_trivially_constructible was.
        typet dest = to_reference_type(t1).base_type();
        typet src = t2;
        if(is_reference(src) || is_rvalue_reference(src))
          src = to_pointer_type(src).base_type();
        dest.remove(ID_C_constant);
        dest.remove(ID_C_volatile);
        src.remove(ID_C_constant);
        src.remove(ID_C_volatile);
        if(dest.id() == ID_struct_tag || dest.id() == ID_union_tag)
        {
          assignable =
            (src.id() == dest.id() && to_tag_type(src).get_identifier() ==
                                        to_tag_type(dest).get_identifier()) &&
            is_trivially_copyable_type(dest, false, 64);
        }
      }
      // __is_nothrow_assignable: nothrow is about exceptions, which the
      // front end does not model; assignable suffices.
      expr = assignable ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_trivially_constructible" ||
      expr.id() == "__is_nothrow_constructible")
    {
      // Delegate to __is_constructible logic: trivially/nothrow
      // qualifiers are about optimization, not correctness.
      // For POD/scalar types with matching args, return true.
      typet class_t1 = t1;
      class_t1.remove(ID_C_constant);
      class_t1.remove(ID_C_volatile);
      if(
        t2.is_nil() && expr.id() == "__is_nothrow_constructible" &&
        class_t1.id() == ID_struct_tag)
      {
        // N5008 [meta.unary.prop]: is_nothrow_constructible<T> is
        // is_constructible<T> and the definition `T t;' is known not to
        // throw ([except.spec]/8 for the implicit or defaulted default
        // constructor)
        elaborate_class_template(class_t1);
        bool constructible = true;
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        try
        {
          sfinae_contextt sfinae_guard{*this};
          symbol_exprt object{irep_idt{}, t1};
          object.set(ID_C_lvalue, true);
          cpp_constructor(expr.source_location(), object, {});
        }
        catch(...)
        {
          constructible = false;
        }
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
        expr = constructible && default_construction_is_nothrow(class_t1, 16)
                 ? exprt(true_exprt())
                 : exprt(false_exprt());
      }
      else if(t2.is_nil())
      {
        // __is_trivially_constructible(T) — default constructible
        // A type is trivially default constructible if it has no
        // user-provided default constructor.
        bool trivial = true;
        if(t1.id() == ID_struct_tag)
        {
          const auto &st = follow_tag(to_struct_tag_type(t1));
          for(const auto &c : st.components())
          {
            if(
              c.type().id() == ID_code &&
              to_code_type(c.type()).return_type().id() == ID_constructor &&
              to_code_type(c.type()).parameters().size() == 1)
            {
              // Found a default constructor (only 'this' param).
              // Check if it has a non-trivial body in the symbol table.
              const auto *sym = symbol_table.lookup(c.get_name());
              if(sym != nullptr && sym->value.is_not_nil())
              {
                trivial = false;
                break;
              }
            }
          }
        }
        expr = trivial ? exprt(true_exprt()) : exprt(false_exprt());
      }
      else if(expr.id() == "__is_trivially_constructible")
      {
        // N5008 [meta.unary.prop]: is_trivially_constructible<T, Args...>
        // -- is_constructible and the variable definition calls no
        // non-trivial operation.  For the copy/move case (one argument of
        // the same class type, [class.copy.ctor]/11) that is: the class
        // has no user-provided copy/move constructor and its bases and
        // members are trivially copyable -- is_trivially_copyable_type.
        // Was an unconditional TRUE, so `NT(const NT &)' counted as
        // trivially copy constructible (libc++ variant's trait).
        typet u = t2;
        if(is_reference(u))
          u = to_reference_type(u).base_type();
        u.remove(ID_C_constant);
        u.remove(ID_C_volatile);
        typet t1_plain = t1;
        t1_plain.remove(ID_C_constant);
        t1_plain.remove(ID_C_volatile);
        const bool same_class = t1_plain.id() == ID_struct_tag &&
                                u.id() == ID_struct_tag &&
                                to_struct_tag_type(t1_plain).get_identifier() ==
                                  to_struct_tag_type(u).get_identifier();
        if(same_class)
          expr = is_trivially_copyable_type(t1_plain, false, 16)
                   ? exprt(true_exprt())
                   : exprt(false_exprt());
        else if(t1_plain.id() == ID_struct_tag || t1_plain.id() == ID_union_tag)
          expr = false_exprt(); // converting construction: a call
        else
          expr = true_exprt(); // a scalar from a scalar
      }
      else
      {
        // __is_nothrow_constructible(T, U): nothrow is about exceptions,
        // which are not modelled
        expr = true_exprt();
      }
    }
    else if(expr.id() == "__is_nothrow_convertible")
    {
      // Same as __is_convertible — nothrow is about optimization.
      if(t1.id() == ID_empty && t2.id() == ID_empty)
        expr = true_exprt();
      else if(t1.id() == ID_empty || t2.id() == ID_empty)
        expr = false_exprt();
      else
      {
        exprt tmp;
        // See the declval note in __is_convertible above.
        typet from_type = t1;
        if(is_reference(from_type))
          from_type = to_reference_type(from_type).base_type();
        symbol_exprt from(irep_idt(), from_type);
        // [meta.unary.prop], [over.match.copy]/1: the synthesised declval<>()
        // operand is a class prvalue that may need to bind as the implicit
        // object argument of a source-side conversion function; mark it so
        // reference_binding materialises a temporary for that `this` binding.
        from.set(ID_C_temporary_avoided, true);
        if(is_reference(t1) && !is_rvalue_reference(t1))
          from.set(ID_C_lvalue, true);
        if(implicit_conversion_sequence(from, t2, tmp))
          expr = true_exprt();
        else
          expr = false_exprt();
      }
    }
    else if(expr.id() == "__is_constructible")
    {
      // __is_constructible(T, Args...) — check if T can be constructed
      // from Args. For scalar types, construction from a compatible type
      // (including references) is always possible.
      //
      // N5008 [temp.variadic]/5: an empty pack expansion in the argument list
      // (e.g. `__is_constructible(T, Args...)` with an empty `Args`, which is
      // how `std::is_default_constructible<T>` = `is_constructible<T>` and the
      // SFINAE default template argument of std::stack's default constructor
      // are written) contributes no arguments.  An empty pack leaves
      // `type_arg2` as the (now empty) pack NAME, which type-checks to the
      // empty type rather than to nil.  Detect this precisely -- the raw
      // second type argument is a cpp_name that resolved to the empty type --
      // and treat it as "no second argument" (the default-constructibility
      // query), matching the direct `__is_constructible(T)` form.  A genuine
      // argument type (including an explicit `void`, whose raw form is a type
      // keyword, not a cpp_name) is left to the construction check below.
      const bool empty_pack_second_arg =
        t2.id() == ID_empty && expr.find("type_arg2").id() == ID_cpp_name;
      typet class_t1 = t1;
      class_t1.remove(ID_C_constant);
      class_t1.remove(ID_C_volatile);
      if(
        (t2.is_nil() || empty_pack_second_arg) &&
        class_t1.id() == ID_struct_tag)
      {
        // N5008 [meta.unary.prop]/9: is_constructible<T> holds iff the
        // definition `T t;' would be well-formed, considering only the
        // immediate context.  For a class this is overload resolution among
        // its constructors for an empty argument list, including constructor
        // templates whose default template arguments fail to substitute
        // ([temp.deduct.general]/8) -- libstdc++'s pair default constructor
        // is constrained on is_default_constructible of its element type.
        // Attempt that construction as a substitution context.
        elaborate_class_template(class_t1);
        bool constructible = true;
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        try
        {
          sfinae_contextt sfinae_guard{*this};
          symbol_exprt object{irep_idt{}, t1};
          object.set(ID_C_lvalue, true);
          cpp_constructor(expr.source_location(), object, {});
        }
        catch(...)
        {
          constructible = false;
        }
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
        expr = constructible ? static_cast<exprt>(true_exprt())
                             : static_cast<exprt>(false_exprt());
      }
      else if(t2.is_nil())
      {
        // Default constructible — scalars are always default constructible
        expr = true_exprt();
      }
      else if(empty_pack_second_arg)
      {
        // is_constructible<T> (empty argument pack) is default-constructibility
        // ([meta.unary.prop]).  Evaluate it accurately for class types: a class
        // with a user-declared constructor but no default constructor is NOT
        // default-constructible.  (The direct `t2.is_nil()` branch above
        // over-approximates to true for compatibility; here we must be precise,
        // because reporting a non-default-constructible class as constructible
        // selects a construction that does not exist -- e.g. it exposed a crash
        // in std::regex's error_category handling.)
        typet dt = t1;
        dt.remove(ID_C_constant);
        dt.remove(ID_C_volatile);
        if(dt.id() == ID_struct_tag)
        {
          const struct_typet &st = follow_tag(to_struct_tag_type(dt));
          bool has_user_ctor = false;
          bool has_default_ctor = false;
          for(const auto &c : st.components())
          {
            if(c.type().id() != ID_code || c.get_bool(ID_from_base))
              continue;
            if(to_code_type(c.type()).return_type().id() != ID_constructor)
              continue;
            has_user_ctor = true;
            const auto &ps = to_code_type(c.type()).parameters();
            if(ps.size() == 1 && ps.front().get_this())
            {
              has_default_ctor = true;
              break;
            }
          }
          // No constructor at all -> implicit default constructor; a default
          // constructor present -> default-constructible; otherwise not.
          expr = (!has_user_ctor || has_default_ctor)
                   ? static_cast<exprt>(true_exprt())
                   : static_cast<exprt>(false_exprt());
        }
        else
        {
          // Scalars, pointers, enums, arrays: default-constructible.
          expr = true_exprt();
        }
      }
      else
      {
        // Strip references from the argument type
        typet arg_type = t2;
        if(is_reference(arg_type))
          arg_type = to_reference_type(arg_type).base_type();
        arg_type.remove(ID_C_constant);
        arg_type.remove(ID_C_volatile);

        typet target = t1;
        target.remove(ID_C_constant);
        target.remove(ID_C_volatile);

        if(target == arg_type)
          expr = true_exprt();
        else
        {
          exprt tmp;
          // N5008 [meta.unary.prop]: the trait is defined in terms of
          // `declval<Args>()`, i.e. a value of the argument type.  Build the
          // source expression from the de-referenced argument type (preserving
          // cv-qualifiers): a source expression whose type is itself a
          // reference (e.g. `pair<int,int>&&`) fails to bind to a converting
          // constructor's reference parameter (`pair(pair<U1,U2>&&)`) during
          // implicit_conversion_sequence, whereas the de-referenced value type
          // binds as the by-value argument case already does.  Without this,
          // is_constructible<pair<const int,int>, pair<int,int>&&> -- the guard
          // on std::map / std::unordered_map's `insert(_Pair&&)` overload --
          // was wrongly reported false.
          typet from_type = t2;
          if(is_reference(from_type))
            from_type = to_reference_type(from_type).base_type();
          symbol_exprt from(irep_idt(), from_type);
          from.set(ID_C_temporary_avoided, true);
          // N5008 [meta.unary.prop]: is_constructible<T, Args...> is defined
          // via
          // `declval<Args>()`, whose value category is an lvalue iff the
          // corresponding Arg is an lvalue-reference type, and an xvalue
          // (rvalue) otherwise.  Preserve that here: it decides how a
          // forwarding-reference constructor parameter `U&&` deduces its
          // template argument (an lvalue argument deduces `U = int&`, an rvalue
          // deduces `U = int`), which in turn drives SFINAE constraints that
          // reject rvalues.  For example std::reference_wrapper<const T> guards
          // its converting constructor with an overload set that deletes the
          // rvalue form, so it is constructible from `T&` but not from `T&&` /
          // `T`; without marking the lvalue-reference case as an lvalue,
          // is_constructible<reference_wrapper<const int>, int&> was wrongly
          // reported false (the forwarding reference deduced the rvalue form
          // and
          // selected the deleted overload).
          if(is_reference(t2) && !is_rvalue_reference(t2))
            from.set(ID_C_lvalue, true);
          if(implicit_conversion_sequence(from, t1, tmp))
            expr = true_exprt();
          else
            expr = false_exprt();
        }
      }
    }
    else if(
      expr.id() == "__reference_constructs_from_temporary" ||
      expr.id() == "__reference_converts_from_temporary")
    {
      // P2255R2 / N5008 [meta.rel] tab:meta.rel: true iff T (t1) is a
      // reference type bound to a value of type U (t2) via a
      // MATERIALIZED TEMPORARY ([dcl.init.ref]/5.4,
      // [class.temporary]).  Approximation without user-defined
      // conversions:
      //  * T not a reference, or U nil/void -> false;
      //  * U a reference type: the initializer is a glvalue; a
      //    reference-compatible binding creates no temporary -> false;
      //  * U a non-reference (prvalue): a temporary is materialized
      //    unless T is a non-const lvalue reference (which cannot bind
      //    a temporary, [dcl.init.ref]/5.1) -> true for `const T&` and
      //    `T&&` on the same (up to cv) or derived-to-base type.
      bool result = false;
      if(is_reference(t1) && t2.is_not_nil() && t2.id() != ID_empty)
      {
        if(!is_reference(t2))
        {
          const typet &referred = to_reference_type(t1).base_type();
          const bool t1_is_rvalue_ref = is_rvalue_reference(t1);
          const bool referred_const = referred.get_bool(ID_C_constant);
          if(t1_is_rvalue_ref || referred_const)
          {
            typet a = referred, b = t2;
            a.remove(ID_C_constant);
            a.remove(ID_C_volatile);
            b.remove(ID_C_constant);
            b.remove(ID_C_volatile);
            if(a == b)
              result = true;
            else if(a.id() == ID_struct_tag && b.id() == ID_struct_tag)
              result = subtype_typecast(
                follow_tag(to_struct_tag_type(b)),
                follow_tag(to_struct_tag_type(a)));
          }
        }
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__reference_binds_to_temporary")
    {
      // Clang's `__reference_binds_to_temporary(T, U)': true iff the
      // initialization `T t(VAL<U>);' ([meta.rqmts]/5: VAL<U> has the type
      // and value category of declval<U>(), a prvalue for a non-reference
      // U) is well-formed and binds t to a temporary that the initializer
      // was CONVERTED to -- N5008 [dcl.init.ref]/5.3.2 with a conversion
      // function to a prvalue, /5.4.1 (user-defined conversion) or /5.4.2
      // (standard conversion to a prvalue of T1).  A prvalue of the
      // referenced type or of a class derived from it (/5.3.1) is
      // materialized ([conv.rval]) but not converted, and yields false, as
      // does a direct lvalue binding (/5.1) and a conversion function
      // returning a reference (/5.1.2, /5.3.2 lvalue).  Distinct from
      // [meta.unary.prop] reference_constructs_from_temporary, which is
      // true for the materialized prvalue as well.
      bool result = false;
      if(
        is_reference(t1) && t2.is_not_nil() && t2.id() != ID_empty &&
        t2.id() != ID_code)
      {
        typet from_type = t2;
        if(is_reference(from_type))
          from_type = to_reference_type(from_type).base_type();
        symbol_exprt probe{irep_idt{}, from_type};
        probe.set(ID_C_temporary_avoided, true);
        probe.set("#reference_binds_probe", true);
        if(is_reference(t2) && !is_rvalue_reference(t2))
          probe.set(ID_C_lvalue, true);
        exprt bound;
        unsigned rank = 0;
        bool ok = false;
        try
        {
          sfinae_contextt sfinae_guard{*this};
          unevaluated_operandt unevaluated_guard{*this};
          ok = reference_binding(probe, to_reference_type(t1), bound, rank);
        }
        catch(...)
        {
        }
        if(ok)
        {
          // walk to the object the reference is bound to: through the
          // address (and a derived-to-base cast of the address), the
          // materialization of a prvalue and an implicit dereference; a
          // cast of the OBJECT is a standard conversion ([dcl.init.ref]
          // /5.4.2) and stops the walk
          const exprt *object = &bound;
          while(true)
          {
            if(object->id() == ID_typecast && is_reference(object->type()))
              object = &to_typecast_expr(*object).op();
            else if(
              object->id() == ID_address_of || object->id() == ID_dereference)
            {
              object = &to_unary_expr(*object).op();
            }
            else if(
              object->id() == ID_side_effect &&
              object->get(ID_statement) == ID_temporary_object &&
              object->operands().size() == 1)
            {
              object = &to_unary_expr(*object).op();
            }
            else
              break;
          }
          // the initializer itself (or its base class subobject), or the
          // glvalue result of a conversion function returning a reference:
          // bound directly
          const bool direct = object->get_bool("#reference_binds_probe") ||
                              is_reference(object->type());
          result = !direct;
        }
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else
      // conservatively return false for traits we cannot evaluate
      expr = false_exprt();
  }
  else if(expr.id() == ID_cpp_datasizeof)
  {
    // Clang's `__datasizeof(T)': the Itanium C++ ABI's dsize(T), "the size
    // of an object of type T without tail padding" (ABI 2.2).  ABI 2.4-II:
    // for a class that is a POD for the purpose of layout (a C++03 POD:
    // N5008 [class.prop] trivial + standard-layout as of C++03 -- no
    // user-declared special members, bases, virtual members or non-public
    // non-static data members) dsize is sizeof; otherwise it is the end of
    // the last non-static data member, 0 for an empty class, since a
    // derived class may place its own members in the tail padding.  For a
    // non-class type dsize is sizeof ([expr.sizeof]/1-2).  libc++ 18
    // preprocessed by clang selects `__libcpp_datasizeof<_Tp>::value =
    // __datasizeof(_Tp)' and sizes every basic_string copy with it.
    complete_type_operand(expr);
    throw_if_incomplete_dependency(expr);
    typet &type = static_cast<typet &>(expr.add(ID_type_arg));
    typecheck_type(type); // unwraps the already_typechecked marker
    std::optional<exprt> result;
    if(type.id() == ID_struct_tag && !cpp_is_pod(type))
    {
      // the end of the last non-static data member: the layout's trailing
      // padding component(s) are exactly the tail padding
      const struct_typet &struct_type = follow_tag(to_struct_tag_type(type));
      result = from_integer(0, size_type());
      const auto &components = struct_type.components();
      for(auto it = components.rbegin(); it != components.rend(); ++it)
      {
        if(it->get_is_padding() || it->type().id() == ID_code)
          continue;
        auto offset = member_offset_expr(struct_type, it->get_name(), *this);
        auto size = size_of_expr(it->type(), *this);
        if(offset.has_value() && size.has_value())
        {
          result = plus_exprt{
            typecast_exprt::conditional_cast(*offset, size_type()),
            typecast_exprt::conditional_cast(*size, size_type())};
        }
        else
          result.reset();
        break;
      }
    }
    else
      result = size_of_expr(type, *this); // a union has no tail padding
    if(!result.has_value())
    {
      error().source_location = expr.source_location();
      error() << "__datasizeof of type '" << to_string(type)
              << "' has no known size" << eom;
      throw 0;
    }
    result->add_source_location() = expr.source_location();
    simplify(*result, *this);
    expr.swap(*result);
  }
  else if(expr.id() == ID_noexcept)
  {
    // C++11 noexcept operator per [expr.unary.noexcept]/3: "The
    // result of the noexcept operator is a prvalue of type bool.
    // Its value is false if the expression would throw because of
    // …; otherwise it is true."  Evaluating the operand for this
    // determination is an unevaluated operand ([basic.def.odr]/2,
    // [expr.context]/1) and substitution failures must not leak
    // as diagnostics — treat it as a SFINAE immediate context.
    auto &op = to_unary_expr(expr).op();
    bool result = false;

    try
    {
      sfinae_contextt sfinae_guard{*this};
      // [expr.unary.noexcept]/1: the operand is unevaluated
      unevaluated_operandt unevaluated_guard{*this};
      typecheck_expr(op);
      // [expr.unary.noexcept]/3 + [except.spec]/6: the operand is
      // potentially-throwing if it contains, at any depth, a call to a
      // function that is not non-throwing, a throw-expression, or a
      // dynamic_cast / typeid that can throw.  A destructor is
      // non-throwing unless declared otherwise ([except.spec]/8).
      // Previously only a top-level call was examined, so `noexcept(p < q)'
      // rewritten to `(p <=> q) < 0' read only the category's noexcept
      // operator< and ignored the potentially-throwing operator<=> inside.
      std::function<bool(const exprt &)> potentially_throwing =
        [&](const exprt &e) -> bool
      {
        if(e.id() == ID_side_effect)
        {
          const irep_idt &statement = e.get(ID_statement);
          if(statement == ID_throw)
            return true;
          if(statement == ID_function_call)
          {
            const auto &fn = to_side_effect_expr_function_call(e).function();
            bool non_throwing = false;
            if(fn.id() == ID_symbol)
            {
              const auto *sym =
                symbol_table.lookup(to_symbol_expr(fn).get_identifier());
              if(sym != nullptr && sym->type.id() == ID_code)
              {
                const auto &code_type = to_code_type(sym->type);
                non_throwing = code_type.get_bool("#C_noexcept") ||
                               code_type.get_bool(ID_noexcept) ||
                               code_type.return_type().id() == ID_destructor;
              }
            }
            else if(
              fn.id() == ID_member &&
              fn.find(ID_component_cpp_name).is_not_nil())
            {
              // a destructor call spelled `x.~T()'
              const auto &name = to_cpp_name(fn.find(ID_component_cpp_name));
              const irep_idt &bn = name.get_base_name();
              non_throwing = !bn.empty() && id2string(bn)[0] == '~';
            }
            else if(fn.type().id() == ID_code)
            {
              const auto &code_type = to_code_type(fn.type());
              non_throwing = code_type.get_bool("#C_noexcept") ||
                             code_type.get_bool(ID_noexcept);
            }
            if(!non_throwing)
              return true;
          }
        }
        for(const auto &sub : e.operands())
          if(potentially_throwing(sub))
            return true;
        return false;
      };
      result = !potentially_throwing(op);
    }
    catch(...)
    {
      // Substitution failure inside noexcept is a SFINAE failure
      // that in turn makes the noexcept-expr evaluate to `true`
      // (the operand can't throw because it can't even exist).
      result = true;
    }
    if(result)
      expr = true_exprt();
    else
      expr = false_exprt();
  }
  else if(expr.id() == ID_initializer_list)
  {
    // Preserve the type if it was already set (e.g., from a
    // brace-init-list for aggregate initialization).
    if(expr.type().is_nil() || expr.type().id() == ID_empty)
      expr.type().id(ID_initializer_list);
  }
  else if(
    expr.id() == ID_const_cast || expr.id() == ID_dynamic_cast ||
    expr.id() == ID_reinterpret_cast || expr.id() == ID_static_cast)
  {
    typecheck_cast_expr(expr);
  }
  else if(expr.id() == "__is_abstract")
  {
    typet t;
    if(!expr.find(ID_type_arg).is_nil())
      t = static_cast<const typet &>(expr.find(ID_type_arg));
    else if(!expr.find("type_arg1").is_nil())
      t = static_cast<const typet &>(expr.find("type_arg1"));
    typecheck_type(t);
    // A class is abstract if it has at least one pure virtual function.
    if(t.id() == ID_struct_tag)
    {
      const struct_typet &st =
        to_struct_type(follow_tag(to_struct_tag_type(t)));
      bool is_abstract = false;
      for(const auto &c : st.components())
      {
        if(c.get_bool(ID_is_pure_virtual))
        {
          is_abstract = true;
          break;
        }
      }
      expr = is_abstract ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else
      expr = false_exprt();
  }
  else if(
    expr.id() == "__is_class" || expr.id() == "__is_empty" ||
    expr.id() == "__is_enum" || expr.id() == "__is_final" ||
    expr.id() == "__is_aggregate" || expr.id() == "__is_pod" ||
    expr.id() == "__is_polymorphic" || expr.id() == "__is_union" ||
    expr.id() == "__is_trivial" || expr.id() == "__is_trivially_copyable" ||
    expr.id() == "__is_standard_layout" || expr.id() == "__is_literal_type" ||
    expr.id() == "__is_integral" || expr.id() == "__is_void" ||
    expr.id() == "__is_floating_point" || expr.id() == "__is_arithmetic" ||
    expr.id() == "__is_null_pointer" || expr.id() == "__is_pointer" ||
    expr.id() == "__is_reference" || expr.id() == "__is_lvalue_reference" ||
    expr.id() == "__is_rvalue_reference" || expr.id() == "__is_function" ||
    expr.id() == "__is_array" || expr.id() == "__is_member_pointer" ||
    expr.id() == "__is_member_function_pointer" ||
    expr.id() == "__is_member_object_pointer" || expr.id() == "__is_signed" ||
    expr.id() == "__is_unsigned" || expr.id() == "__is_const" ||
    expr.id() == "__is_volatile" || expr.id() == "__is_scoped_enum" ||
    expr.id() == "__is_object" || expr.id() == "__is_bounded_array" ||
    expr.id() == "__is_unbounded_array" || expr.id() == "__is_referenceable" ||
    expr.id() == "__has_trivial_constructor" ||
    expr.id() == "__has_trivial_copy" ||
    expr.id() == "__has_trivial_destructor" ||
    expr.id() == "__has_trivial_assign" ||
    expr.id() == "__has_nothrow_assign" ||
    expr.id() == "__has_nothrow_constructor" ||
    expr.id() == "__has_nothrow_copy" ||
    expr.id() == "__has_virtual_destructor" ||
    expr.id() == "__has_unique_object_representations" ||
    expr.id() == "__is_trivially_relocatable" ||
    expr.id() == "__is_trivially_destructible" ||
    expr.id() == "__is_destructible" ||
    expr.id() == "__is_nothrow_destructible" || expr.id() == "__is_compound" ||
    expr.id() == "__is_fundamental" || expr.id() == "__is_scalar")
  {
    // Unary type predicates — conservatively return false for now.
    typet t;
    if(!expr.find(ID_type_arg).is_nil())
      t = static_cast<const typet &>(expr.find(ID_type_arg));
    else if(!expr.find("type_arg1").is_nil())
      t = static_cast<const typet &>(expr.find("type_arg1"));
    typecheck_type(t);
    if(expr.id() == "__is_class")
      expr =
        (t.id() == ID_struct_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_union")
      expr =
        (t.id() == ID_union_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_enum")
      expr =
        (t.id() == ID_c_enum_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_final")
    {
      bool is_final = false;
      if(t.id() == ID_struct_tag)
      {
        const auto &struct_type = follow_tag(to_struct_tag_type(t));
        is_final = struct_type.get_bool(ID_final);
      }
      expr = is_final ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_integral")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool || t.id() == ID_bool || t.id() == ID_c_enum_tag)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_floating_point")
    {
      expr = (t.id() == ID_floatbv || t.id() == ID_fixedbv)
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_arithmetic")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool || t.id() == ID_bool || t.id() == ID_floatbv ||
         t.id() == ID_fixedbv || t.id() == ID_c_enum_tag)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_void")
    {
      expr = (t.id() == ID_empty) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_pointer")
    {
      expr = (t.id() == ID_pointer && !is_reference(t)) ? exprt(true_exprt())
                                                        : exprt(false_exprt());
    }
    else if(expr.id() == "__is_reference")
    {
      expr = is_reference(t) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_lvalue_reference")
    {
      expr = (is_reference(t) && !is_rvalue_reference(t))
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_rvalue_reference")
    {
      expr =
        is_rvalue_reference(t) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_array")
    {
      expr = (t.id() == ID_array) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_function")
    {
      expr = (t.id() == ID_code) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_member_pointer" ||
      expr.id() == "__is_member_function_pointer" ||
      expr.id() == "__is_member_object_pointer")
    {
      bool is_memptr =
        t.id() == ID_pointer && t.find(ID_to_member).is_not_nil();
      if(is_memptr && expr.id() == "__is_member_function_pointer")
        is_memptr = to_pointer_type(t).base_type().id() == ID_code;
      else if(is_memptr && expr.id() == "__is_member_object_pointer")
        is_memptr = to_pointer_type(t).base_type().id() != ID_code;
      expr = is_memptr ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_null_pointer")
    {
      expr = (t.id() == ID_pointer && t == pointer_type(empty_typet()))
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_signed")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_fixedbv || t.id() == ID_floatbv)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_unsigned")
    {
      expr =
        (t.id() == ID_unsignedbv || t.id() == ID_c_bool || t.id() == ID_bool)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_const")
    {
      expr =
        t.get_bool(ID_C_constant) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_volatile")
    {
      expr =
        t.get_bool(ID_C_volatile) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_scoped_enum")
    {
      bool result = false;
      if(t.id() == ID_c_enum_tag)
      {
        const auto &enum_type =
          to_c_enum_type(follow_tag(to_c_enum_tag_type(t)));
        result = enum_type.get_bool(ID_C_class);
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_object")
    {
      // true for everything except functions, references, and void
      bool result = t.id() != ID_code && t.id() != ID_empty &&
                    !is_reference(t) && !is_rvalue_reference(t);
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_bounded_array")
    {
      bool result = t.id() == ID_array && to_array_type(t).size().is_not_nil();
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_unbounded_array")
    {
      bool result = t.id() == ID_array && to_array_type(t).size().is_nil();
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__has_trivial_destructor" ||
      expr.id() == "__is_trivially_destructible")
    {
      // [class.prop]/1 + [class.dtor]/8: trivially destructible iff scalar,
      // array thereof, or a class whose destructor is trivial (not virtual,
      // not user-provided) and whose bases/members are all trivially
      // destructible.  libstdc++ is_trivially_destructible uses
      // __has_trivial_destructor, so an unconditional false was unsound.
      std::function<bool(const typet &, int)> trivially_destructible =
        [&](const typet &type, int depth) -> bool
      {
        if(depth <= 0)
          return true;
        if(type.id() == ID_array)
          return trivially_destructible(
            to_array_type(type).element_type(), depth - 1);
        if(type.id() != ID_struct_tag)
          return true;
        const auto &st = follow_tag(to_struct_tag_type(type));
        if(st.get_bool(ID_incomplete))
          return true;
        for(const auto &comp : to_struct_type(st).components())
        {
          if(comp.get_bool(ID_is_static) || comp.get_bool(ID_is_type))
            continue;
          if(comp.get_bool(ID_is_vtptr))
            continue;
          if(comp.type().id() == ID_code)
          {
            if(to_code_type(comp.type()).return_type().id() == ID_destructor)
            {
              if(comp.get_bool(ID_is_virtual))
                return false;
              if(!comp.type().get_bool("#is_implicit_dtor"))
                return false;
            }
            continue;
          }
          if(!trivially_destructible(comp.type(), depth - 1))
            return false;
        }
        return true;
      };
      expr = trivially_destructible(t, 64) ? exprt(true_exprt())
                                           : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_nothrow_destructible" ||
      expr.id() == "__is_destructible")
    {
      bool result = true;
      if(t.id() == ID_struct_tag)
      {
        const auto &st = follow_tag(to_struct_tag_type(t));
        for(const auto &comp : to_struct_type(st).components())
          if(comp.get_bool(ID_destructor))
          {
            result = false;
            break;
          }
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_empty" || expr.id() == "__is_polymorphic" ||
      expr.id() == "__has_virtual_destructor" ||
      expr.id() == "__is_standard_layout" || expr.id() == "__is_pod" ||
      expr.id() == "__is_aggregate" || expr.id() == "__is_literal_type")
    {
      // The class properties of N5008 [class.prop], [class.virtual]/1,
      // [class.dtor]/9 and [dcl.init.aggr]/1, on the flattened struct
      // (base members are components marked #from_base; a polymorphic class
      // has a vtable-pointer component).  Every one of these was
      // unconditionally false, so libstdc++'s is_empty (the empty-base /
      // by-value-functor selections: `__by_ref_or_value_fn' in
      // predefined_ops.h, compressed_pair) picked the wrong alternative.
      expr = class_property(expr.id(), t) ? exprt(true_exprt())
                                          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_referenceable")
    {
      // [defns.referenceable]: an object type, a function type without
      // cv/ref-qualifiers, or a reference type -- everything but void
      // (and cv void)
      expr = t.id() == ID_empty ? exprt(false_exprt()) : exprt(true_exprt());
    }
    else if(expr.id() == "__is_compound")
    {
      bool f = t.id() == ID_empty || t.id() == ID_signedbv ||
               t.id() == ID_unsignedbv || t.id() == ID_c_bool ||
               t.id() == ID_bool || t.id() == ID_floatbv ||
               t.id() == ID_fixedbv;
      expr = !f ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_fundamental")
    {
      bool r = t.id() == ID_empty || t.id() == ID_signedbv ||
               t.id() == ID_unsignedbv || t.id() == ID_c_bool ||
               t.id() == ID_bool || t.id() == ID_floatbv ||
               t.id() == ID_fixedbv;
      expr = r ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_scalar")
    {
      bool r = t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
               t.id() == ID_c_bool || t.id() == ID_bool ||
               t.id() == ID_floatbv || t.id() == ID_fixedbv ||
               t.id() == ID_c_enum_tag ||
               (t.id() == ID_pointer && !is_reference(t));
      expr = r ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_trivially_copyable" || expr.id() == "__is_trivial")
    {
      // N5008 [basic.types.general]/9: scalar types, trivially copyable
      // class types, arrays of such, and cv-qualified versions are
      // trivially copyable; the trivial types add trivially default
      // constructible classes.  Used to be an unconditional false -- so
      // libc++'s variant computed a non-trivial copy for variant<int,
      // double>, and std::is_trivially_copyable<int> was false.
      const bool want_trivial = expr.id() == "__is_trivial";
      expr = is_trivially_copyable_type(t, want_trivial, 16)
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else
      expr = false_exprt();
  }
  else if(expr.id() == "lambda")
  {
    typecheck_expr_lambda(expr);
  }
  else if(expr.id() == ID_index)
  {
    // C++23 multidimensional subscript: struct[args] → operator[](args)
    auto &index_expr = to_binary_expr(expr);
    typecheck_expr_main(index_expr.op0());
    const typet &t = index_expr.op0().type();
    if(t.id() == ID_struct_tag || t.id() == ID_struct)
    {
      // Build operator[] call
      exprt op_name(ID_cpp_name);
      irept op_node(ID_operator);
      op_name.get_sub().push_back(op_node);
      irept bracket_node("[]");
      op_name.get_sub().push_back(bracket_node);

      exprt member(ID_member);
      member.add_to_operands(index_expr.op0());
      member.add(ID_component_cpp_name, op_name);

      // Collect arguments: if the index is a comma expression, split it
      exprt::operandst args;
      exprt &idx = index_expr.op1();
      if(idx.id() == ID_comma)
      {
        // Flatten comma expression into argument list
        std::function<void(exprt &)> flatten = [&](exprt &e)
        {
          if(e.id() == ID_comma)
          {
            flatten(to_binary_expr(e).op0());
            flatten(to_binary_expr(e).op1());
          }
          else
            args.push_back(e);
        };
        flatten(idx);
      }
      else
        args.push_back(idx);

      side_effect_expr_function_callt call(
        std::move(member), std::move(args), typet{}, expr.source_location());
      typecheck_side_effect_function_call(call);
      expr.swap(call);
    }
    else
      c_typecheck_baset::typecheck_expr_main(expr);
  }
  else
    c_typecheck_baset::typecheck_expr_main(expr);
} // NOLINT(readability/fn_size)

void cpp_typecheckt::typecheck_expr_trinary(if_exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);

  implicit_typecast_bool(expr.op0()); // [conv.general]/4, [expr.cond]/1

  if(expr.op1().type().id() == ID_empty || expr.op1().type().id() == ID_empty)
  {
    if(expr.op1().get_bool(ID_C_lvalue))
    {
      exprt e1(expr.op1());
      if(!standard_conversion_lvalue_to_rvalue(e1, expr.op1()))
      {
        error().source_location = e1.find_source_location();
        error() << "lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id() == ID_array)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_array_to_pointer(e1, expr.op1()))
      {
        error().source_location = e1.find_source_location();
        error() << "array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id() == ID_code)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_function_to_pointer(e1, expr.op1()))
      {
        error().source_location = e1.find_source_location();
        error() << "function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().get_bool(ID_C_lvalue))
    {
      exprt e2(expr.op2());
      if(!standard_conversion_lvalue_to_rvalue(e2, expr.op2()))
      {
        error().source_location = e2.find_source_location();
        error() << "lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id() == ID_array)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_array_to_pointer(e2, expr.op2()))
      {
        error().source_location = e2.find_source_location();
        error() << "array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id() == ID_code)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_function_to_pointer(e2, expr.op2()))
      {
        error().source_location = expr.find_source_location();
        error() << "function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(
      expr.op1().get(ID_statement) == ID_throw &&
      expr.op2().get(ID_statement) != ID_throw)
      expr.type() = expr.op2().type();
    else if(
      expr.op2().get(ID_statement) == ID_throw &&
      expr.op1().get(ID_statement) != ID_throw)
      expr.type() = expr.op1().type();
    else if(
      expr.op1().type().id() == ID_empty && expr.op2().type().id() == ID_empty)
      expr.type() = void_type();
    else
    {
      error().source_location = expr.find_source_location();
      error() << "bad types for operands" << eom;
      throw 0;
    }
    return;
  }

  // N5008 [expr.cond]/4: operands of the same underlying type that differ
  // in cv-qualification (or value category).  Both glvalues of the same
  // category: the target is the cv-combined type ([conv.qual]) and the
  // result keeps that category -- `b ? w : cw` with `W &w, const W &cw` is
  // an lvalue `const W` (4.1).  Different categories (an lvalue and an
  // xvalue, `b ? declval<int&>() : declval<int&&>()`): 4.3 with /6 -- the
  // result is a prvalue of the cv-combined type.  Both are what libstdc++'s
  // COND-RES (common_reference, iterator concepts) is built on.
  const auto value_category = [](const exprt &e) -> int
  {
    // 0 = prvalue, 1 = lvalue, 2 = xvalue
    // (a materialized class prvalue carries the lvalue mark that lets
    // references bind to it, [class.temporary]/2, but is a prvalue)
    if(!e.get_bool(ID_C_lvalue) || is_class_prvalue_temporary(e))
      return 0;
    if(
      e.id() == ID_dereference && e.get_bool(ID_C_implicit) &&
      e.operands().size() == 1 &&
      is_rvalue_reference(to_dereference_expr(e).pointer().type()))
    {
      return 2;
    }
    return 1;
  };
  typet plain1 = expr.op1().type();
  typet plain2 = expr.op2().type();
  c_qualifierst qual1, qual2;
  qual1.read(plain1);
  qual2.read(plain2);
  c_qualifierst{}.write(plain1);
  c_qualifierst{}.write(plain2);
  const bool same_underlying = plain1 == plain2;

  if(same_underlying)
  {
    c_qualifierst combined = qual1;
    combined += qual2;
    typet result_type = plain1;
    combined.write(result_type);
    expr.type() = result_type;

    const int cat1 = value_category(expr.op1());
    const int cat2 = value_category(expr.op2());
    if(cat1 == cat2 && cat1 != 0)
    {
      // 4.1: same value category; the operands are converted to the
      // cv-combined type without changing their category
      if(expr.op1().type() != result_type)
        expr.op1() = typecast_exprt{expr.op1(), result_type};
      if(expr.op2().type() != result_type)
        expr.op2() = typecast_exprt{expr.op2(), result_type};
      expr.set(ID_C_lvalue, true);
      if(cat1 == 2)
        expr.set(ID_C_xvalue, true);
      return;
    }
    // N5008 [expr.cond]/1, /7: for operands of class type of which one is a
    // prvalue, the result is a prvalue initialized from the selected operand
    // only -- one object is created and the other operand is not evaluated.
    // The front end materializes each prvalue as its own temporary; built as
    // `b ? tmp1 : tmp2', both were constructed (and destroyed) and the result
    // was treated as an lvalue.  Build a single temporary whose initializer
    // initializes it from the selected operand.
    if(expr.type().id() == ID_struct_tag && (cat1 == 0 || cat2 == 0))
    {
      const typet &type = expr.type();
      const source_locationt location = expr.source_location();
      const auto initializer_from = [&](const exprt &operand) -> codet
      {
        if(is_class_prvalue_temporary(operand))
          return to_code(
            static_cast<const exprt &>(operand.find(ID_initializer)));
        exprt object{ID_new_object, type};
        object.set(ID_C_lvalue, true);
        already_typechecked_exprt::make_already_typechecked(object);
        auto code = cpp_constructor(
          location, object, {already_typechecked_exprt{operand}});
        return code.has_value() ? *code : codet{ID_skip};
      };
      code_ifthenelset initialization{
        expr.cond(),
        initializer_from(expr.op1()),
        initializer_from(expr.op2())};
      initialization.add_source_location() = location;
      side_effect_exprt temporary{ID_temporary_object, type, location};
      temporary.set(ID_mode, ID_cpp);
      temporary.set(ID_C_lvalue, true);
      temporary.add(ID_initializer) = std::move(initialization);
      expr.swap(temporary);
      return;
    }

    // 4.3 / 6: a prvalue; lvalue-to-rvalue conversion on glvalue operands.
    // [expr.type]/2: a prvalue of a non-class, non-array type has a
    // cv-unqualified type.
    if(
      result_type.id() != ID_struct_tag && result_type.id() != ID_union_tag &&
      result_type.id() != ID_array)
    {
      result_type = plain1;
      expr.type() = result_type;
    }
    for(exprt *op : {&expr.op1(), &expr.op2()})
    {
      if(op->get_bool(ID_C_lvalue))
      {
        exprt converted;
        if(standard_conversion_lvalue_to_rvalue(*op, converted))
          op->swap(converted);
        else
          op->remove(ID_C_lvalue);
      }
      if(op->type() != result_type)
        *op = typecast_exprt{*op, result_type};
    }
    return;
  }
  else
  {
    exprt e1 = expr.op1();
    exprt e2 = expr.op2();

    if(implicit_conversion_sequence(expr.op1(), expr.op2().type(), e1))
    {
      expr.type() = e1.type();
      expr.op1().swap(e1);
      // Ensure op2 matches the result type (e.g., c_bit_field may
      // differ from the converted type).
      if(expr.op2().type() != expr.type())
        expr.op2() = typecast_exprt::conditional_cast(expr.op2(), expr.type());
    }
    else if(implicit_conversion_sequence(expr.op2(), expr.op1().type(), e2))
    {
      expr.type() = e2.type();
      expr.op2().swap(e2);
      if(expr.op1().type() != expr.type())
        expr.op1() = typecast_exprt::conditional_cast(expr.op1(), expr.type());
    }
    else if(
      expr.op1().type().id() == ID_array &&
      expr.op2().type().id() == ID_array &&
      to_array_type(expr.op1().type()).element_type() ==
        to_array_type(expr.op2().type()).element_type())
    {
      // array-to-pointer conversion

      index_exprt index1(expr.op1(), from_integer(0, c_index_type()));

      index_exprt index2(expr.op2(), from_integer(0, c_index_type()));

      address_of_exprt addr1(index1);
      address_of_exprt addr2(index2);

      expr.op1() = addr1;
      expr.op2() = addr2;
      expr.type() = addr1.type();
      return;
    }
    else
    {
      error().source_location = expr.find_source_location();
      error() << "types are incompatible.\n"
              << "I got '" << type2cpp(expr.op1().type(), *this) << "' and '"
              << type2cpp(expr.op2().type(), *this) << "'." << eom;
      throw 0;
    }
  }

  if(expr.op1().get_bool(ID_C_lvalue) && expr.op2().get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);

  return;
}

/// A temporary object of class type built by the front end for a prvalue
/// (`T(args)', a call result materialized with its constructor call): a
/// temporary_object side effect with an initializer and no operands.
bool cpp_typecheckt::is_class_prvalue_temporary(const exprt &expr)
{
  return expr.id() == ID_side_effect &&
         expr.get(ID_statement) == ID_temporary_object &&
         expr.type().id() == ID_struct_tag && expr.operands().empty() &&
         expr.find(ID_initializer).id() == ID_code;
}

void cpp_typecheckt::typecheck_expr_member(exprt &expr)
{
  typecheck_expr_member(expr, cpp_typecheck_fargst());
}

/// N5008 [temp.variadic]/5: a pack-expansion function-call argument whose
/// pattern names a TYPE template parameter pack (`declval<Args>()...' in
/// `decltype(g(declval<Args>()...))') expands to one argument per element of
/// the pack, the k-th substituting the pack's k-th type.  Function bodies are
/// expanded before type-checking (see cpp_typecheck_method_bodies.cpp); this
/// covers the other contexts -- member declarations of a class template
/// instance and partial-specialization patterns -- where the argument kept
/// its `...' and was type-checked as one argument with the pack's first
/// type.
void cpp_typecheckt::expand_type_pack_arguments(
  exprt &arguments,
  bool with_requires_parameters)
{
  static const std::vector<typet> no_types;
  const auto pack_of = [this, with_requires_parameters](
                         const irept &n) -> const std::vector<typet> *
  {
    if(
      n.id() != ID_cpp_name || n.get_sub().size() != 1 ||
      n.get_sub().front().id() != ID_name)
    {
      return nullptr;
    }
    const irep_idt &base_name = n.get_sub().front().get(ID_identifier);
    for(const auto *id_ptr : cpp_scopes.current_scope().lookup(
          base_name,
          cpp_scopet::RECURSIVE,
          cpp_idt::id_classt::TEMPLATE_PARAMETER))
    {
      const auto it = template_map.pack_args_map.find(id_ptr->identifier);
      if(it != template_map.pack_args_map.end())
        return &it->second;
      // an empty pack is recorded by its size only
      const auto size = template_map.pack_size_map.find(id_ptr->identifier);
      if(size != template_map.pack_size_map.end() && size->second == 0)
        return &no_types;
    }
    // Outside the template's scope (substituting a function template's
    // trailing return type during deduction), the pack is the most
    // recently bound one of that name ([basic.scope.temp]/2), as for
    // template_mapt::expand_call_argument_packs.
    if(with_requires_parameters)
    {
      const std::vector<typet> *newest = nullptr;
      std::size_t newest_generation = 0;
      for(const auto &entry : template_map.pack_args_map)
      {
        const std::string key = id2string(entry.first);
        const auto sep = key.rfind("::");
        if(
          (sep == std::string::npos ? key : key.substr(sep + 2)) !=
          id2string(base_name))
        {
          continue;
        }
        const std::size_t g = template_map.generation_of(entry.first);
        if(newest == nullptr || g > newest_generation)
        {
          newest = &entry.second;
          newest_generation = g;
        }
      }
      return newest;
    }
    return nullptr;
  };
  // the pack a pattern names, and its name
  std::function<const std::vector<typet> *(const irept &, irep_idt &)>
    find_pack =
      [&](const irept &n, irep_idt &name) -> const std::vector<typet> *
  {
    if(const auto *pack = pack_of(n))
    {
      name = n.get_sub().front().get(ID_identifier);
      return pack;
    }
    for(const auto &sub : n.get_sub())
      if(const auto *pack = find_pack(sub, name))
        return pack;
    for(const auto &named_sub : n.get_named_sub())
      if(const auto *pack = find_pack(named_sub.second, name))
        return pack;
    return nullptr;
  };
  std::function<void(irept &, const irep_idt &, const typet &)> substitute =
    [&](irept &n, const irep_idt &name, const typet &element)
  {
    // a type-name is never an operand: replace it only where a type is
    // held (`type' of a cast, of a template argument, ...), including the
    // referenced type of a reference or pointer (`static_cast<A &&>(a)')
    const bool type_node = n.id() == ID_frontend_pointer ||
                           n.id() == ID_pointer || n.id() == ID_merged_type ||
                           n.id() == ID_array;
    for(auto &sub : n.get_sub())
    {
      if(
        type_node && sub.id() == ID_cpp_name && sub.get_sub().size() == 1 &&
        sub.get_sub().front().id() == ID_name &&
        sub.get_sub().front().get(ID_identifier) == name)
      {
        sub = element;
      }
      else
        substitute(sub, name, element);
    }
    for(auto &named_sub : n.get_named_sub())
    {
      if(
        named_sub.second.id() == ID_cpp_name &&
        named_sub.second.get_sub().size() == 1 &&
        named_sub.second.get_sub().front().id() == ID_name &&
        named_sub.second.get_sub().front().get(ID_identifier) == name)
      {
        named_sub.second = element;
      }
      else
        substitute(named_sub.second, name, element);
    }
  };

  // a requires-expression parameter pack named in the pattern
  // (bind_requires_parameter_pack): its k-th element replaces the name
  std::function<const std::vector<exprt> *(const irept &, irep_idt &)>
    find_parameter_pack =
      [&](const irept &n, irep_idt &param) -> const std::vector<exprt> *
  {
    if(
      n.id() == ID_cpp_name && n.get_sub().size() == 1 &&
      n.get_sub().front().id() == ID_name)
    {
      const irep_idt &id = n.get_sub().front().get(ID_identifier);
      const auto it = requires_parameter_packs.find(id);
      // only while a requirement is checked, and only if the name is not
      // bound otherwise (a pack parameter has no symbol of its own name)
      if(
        with_requires_parameters && it != requires_parameter_packs.end() &&
        cpp_scopes.current_scope().lookup(id, cpp_scopet::RECURSIVE).empty())
      {
        param = it->first;
        return &it->second;
      }
    }
    for(const auto &sub : n.get_sub())
      if(const auto *found = find_parameter_pack(sub, param))
        return found;
    return nullptr;
  };
  std::function<void(irept &, const irep_idt &, const exprt &)>
    substitute_parameter =
      [&](irept &n, const irep_idt &param, const exprt &element)
  {
    for(auto &sub : n.get_sub())
    {
      if(
        sub.id() == ID_cpp_name && sub.get_sub().size() == 1 &&
        sub.get_sub().front().id() == ID_name &&
        sub.get_sub().front().get(ID_identifier) == param)
      {
        sub = already_typechecked_exprt{element};
      }
      else
        substitute_parameter(sub, param, element);
    }
  };

  bool changed = false;
  exprt::operandst expanded;
  for(auto &argument : arguments.operands())
  {
    irep_idt name;
    const std::vector<typet> *pack = nullptr;
    irep_idt param;
    const std::vector<exprt> *parameter_pack = nullptr;
    if(argument.get_bool(ID_ellipsis))
    {
      pack = find_pack(argument, name);
      if(with_requires_parameters)
        parameter_pack = find_parameter_pack(argument, param);
    }
    if(
      parameter_pack != nullptr &&
      (pack == nullptr || pack->size() != parameter_pack->size()))
    {
      if(pack != nullptr)
        parameter_pack = nullptr; // inconsistent: leave it as before
    }
    if(pack == nullptr && parameter_pack == nullptr)
    {
      expanded.push_back(argument);
      continue;
    }
    changed = true;
    const std::size_t n =
      pack != nullptr ? pack->size() : parameter_pack->size();
    for(std::size_t k = 0; k < n; ++k)
    {
      exprt copy = argument;
      copy.remove(ID_ellipsis);
      if(pack != nullptr)
        substitute(copy, name, (*pack)[k]);
      if(parameter_pack != nullptr)
      {
        // the argument may be the parameter itself (`h(a...)')
        if(
          copy.id() == ID_cpp_name && copy.get_sub().size() == 1 &&
          copy.get_sub().front().id() == ID_name &&
          copy.get_sub().front().get(ID_identifier) == param)
        {
          copy = already_typechecked_exprt{(*parameter_pack)[k]};
        }
        else
          substitute_parameter(copy, param, (*parameter_pack)[k]);
      }
      expanded.push_back(std::move(copy));
    }
  }
  if(changed)
    arguments.operands() = std::move(expanded);
}

/// The type arguments of a builtin trait recorded by the parser in
/// "type_args" (see Parser::rTypePredicate), typechecked, with a pack
/// expansion `Args...' replaced by the elements of the pack (N5008
/// [temp.variadic]/5); the pack is the template parameter of that name in
/// scope, bound in template_map by the enclosing instantiation.
std::vector<typet> cpp_typecheckt::builtin_trait_type_args(const exprt &expr)
{
  std::vector<typet> result;
  for(const auto &arg : expr.find("type_args").get_sub())
  {
    const typet &raw = static_cast<const exprt &>(arg).type();
    if(
      raw.get_bool(ID_ellipsis) && raw.id() == ID_cpp_name &&
      raw.get_sub().size() == 1 && raw.get_sub().front().id() == ID_name)
    {
      const irep_idt &base_name = raw.get_sub().front().get(ID_identifier);
      bool expanded = false;
      for(const auto *id_ptr : cpp_scopes.current_scope().lookup(
            base_name,
            cpp_scopet::RECURSIVE,
            cpp_idt::id_classt::TEMPLATE_PARAMETER))
      {
        const auto pa = template_map.pack_args_map.find(id_ptr->identifier);
        if(pa != template_map.pack_args_map.end())
        {
          for(const auto &t : pa->second)
            result.push_back(t);
          expanded = true;
          break;
        }
        const auto ps = template_map.pack_size_map.find(id_ptr->identifier);
        if(ps != template_map.pack_size_map.end() && ps->second == 0)
        {
          expanded = true; // an empty pack contributes nothing
          break;
        }
      }
      if(expanded)
        continue;
    }
    typet t = raw;
    t.remove(ID_ellipsis);
    typecheck_type(t);
    if(
      t.id() == ID_empty && raw.id() == ID_cpp_name &&
      raw.get_bool(ID_ellipsis))
      continue; // an empty pack resolved to the empty-pack sentinel
    result.push_back(t);
  }
  return result;
}

/// N5008 [meta.rel]/6-7, [func.require]/1: `__is_invocable(Fn, Args...)'
/// (GCC 14's builtin, libstdc++ 16's std::is_invocable) holds iff
/// INVOKE(declval<Fn>(), declval<Args>()...) is well-formed when treated as
/// an unevaluated operand: for a pointer to member with at least one
/// argument the member is applied to the first argument (an object, a
/// reference or a pointer to it), otherwise Fn is called with the arguments.
/// The nothrow form is treated as the plain form: the front-end does not
/// model exception specifications of calls.
void cpp_typecheckt::typecheck_expr_is_invocable(exprt &expr)
{
  const std::vector<typet> args = builtin_trait_type_args(expr);
  if(args.empty())
  {
    error().source_location = expr.source_location();
    error() << expr.id() << " expects at least one type argument" << eom;
    throw 0;
  }

  // declval<T>(): an lvalue of T for an lvalue reference T, an xvalue
  // otherwise -- the reference is dropped from the operand's type and the
  // lvalue-ness recorded, as the other traits' `from' operands do.
  auto declval = [](const typet &t) -> exprt
  {
    typet base = is_reference(t) ? to_reference_type(t).base_type() : t;
    exprt e{ID_nondet_symbol, base};
    e.set(ID_C_temporary_avoided, true);
    if(is_reference(t) && !is_rvalue_reference(t))
      e.set(ID_C_lvalue, true);
    // not to be looked up or converted again by the probe's typecheck
    return already_typechecked_exprt{std::move(e)};
  };

  const typet fn_type =
    is_reference(args[0]) ? to_reference_type(args[0]).base_type() : args[0];
  if(fn_type.id() == ID_empty)
  {
    expr = false_exprt();
    return;
  }

  exprt probe;
  const bool pointer_to_member =
    fn_type.id() == ID_pointer && fn_type.find(ID_to_member).is_not_nil();
  if(pointer_to_member && args.size() >= 2)
  {
    // (a0.*pm)(a1, ...) resp. a0.*pm for a data member.  The object
    // operand may be a prvalue in the language ([expr.mptr.oper]/2); the
    // front-end's pointer-to-member conversion takes the object's address
    // and so wants an lvalue -- for the probe an lvalue is as good.
    exprt object = declval(args[1]);
    if(!is_reference(args[1]) && args[1].id() != ID_pointer)
      to_already_typechecked_expr(object).get_expr().set(ID_C_lvalue, true);
    exprt pm(ID_pointer_to_member);
    pm.add_to_operands(std::move(object), declval(args[0]));
    pm.add_source_location() = expr.source_location();
    if(to_pointer_type(fn_type).base_type().id() == ID_code)
    {
      side_effect_expr_function_callt call{
        std::move(pm), {}, typet{}, expr.source_location()};
      for(std::size_t i = 2; i < args.size(); ++i)
        call.arguments().push_back(declval(args[i]));
      probe = std::move(call);
    }
    else if(args.size() == 2)
      probe = std::move(pm);
    else
    {
      expr = false_exprt();
      return;
    }
  }
  else
  {
    side_effect_expr_function_callt call{
      declval(args[0]), {}, typet{}, expr.source_location()};
    for(std::size_t i = 1; i < args.size(); ++i)
      call.arguments().push_back(declval(args[i]));
    probe = std::move(call);
  }

  // [temp.deduct]/8: the probe's ill-formedness is a substitution
  // failure, not an error of the program
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  bool invocable = false;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    typecheck_expr(probe);
    invocable = true;
  }
  catch(...)
  {
  }
  get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  expr = invocable ? exprt(true_exprt()) : exprt(false_exprt());
}

void cpp_typecheckt::typecheck_expr_sizeof(exprt &expr)
{
  // We need to overload, "sizeof-expression" can be mis-parsed
  // as a type.

  if(expr.operands().empty())
  {
    const typet &type = static_cast<const typet &>(expr.find(ID_type_arg));

    if(type.id() == ID_cpp_name)
    {
      // [expr.sizeof]/5: a sizeof...(Pack) pack-size query.  Only a genuine
      // `sizeof...` (marked by the parser) counts the pack's elements; a
      // plain `sizeof(type)` whose type happens to be a cpp_name (e.g. a
      // dependent qualified-id such as `first_type<A...>::type`) must compute
      // the type's size, not the number of in-scope pack elements.
      const cpp_namet &cpp_name = to_cpp_name(static_cast<const irept &>(type));
      if(expr.get_bool("#sizeof_pack") && !cpp_name.get_sub().empty())
      {
        const irep_idt &base_name =
          cpp_name.get_sub().front().get(ID_identifier);

        // N5008 [temp.variadic]/8 + [basic.scope.temp]/2: `sizeof...(P)`
        // counts the elements of the pack P named in the *current* scope.
        // Resolve P to its scope-qualified template-parameter identifier and
        // read its size exactly, rather than matching the bare short name
        // against pack_size_map below -- two unrelated templates may each have
        // a pack spelled the same (e.g. several `_Types`), and a short-name
        // match returns whichever sorts first, which can be a different
        // template's pack of a different size and so mis-evaluate the query
        // (e.g. yielding 0 for a one-element pack, turning a would-be-false
        // `__i >= sizeof...(_Types)` SFINAE constraint true).
        {
          const auto id_set = cpp_scopes.current_scope().lookup(
            base_name,
            cpp_scopet::RECURSIVE,
            cpp_idt::id_classt::TEMPLATE_PARAMETER);
          for(const auto *id_ptr : id_set)
          {
            auto it = template_map.pack_size_map.find(id_ptr->identifier);
            if(it != template_map.pack_size_map.end())
            {
              expr = from_integer(it->second, size_type());
              return;
            }
          }
        }

        // Look up pack size by suffix match
        for(const auto &entry : template_map.pack_size_map)
        {
          const std::string &id = id2string(entry.first);
          std::string suffix = "::" + id2string(base_name);
          if(
            id.size() >= suffix.size() &&
            id.compare(id.size() - suffix.size(), suffix.size(), suffix) == 0)
          {
            expr = from_integer(entry.second, size_type());
            return;
          }
        }
        // Fallback: if there's exactly one pack, use it
        if(template_map.pack_size_map.size() == 1)
        {
          expr = from_integer(
            template_map.pack_size_map.begin()->second, size_type());
          return;
        }
      }

      // sizeof(X) may be ambiguous -- X can be either a type or
      // an expression.

      cpp_typecheck_fargst fargs;

      exprt symbol_expr = resolve(
        to_cpp_name(static_cast<const irept &>(type)),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      if(symbol_expr.id() != ID_type)
      {
        expr.copy_to_operands(symbol_expr);
        expr.remove(ID_type_arg);
      }
    }
    else if(type.id() == ID_array)
    {
      // sizeof(expr[index]) can be parsed as an array type!

      if(to_array_type(type).element_type().id() == ID_cpp_name)
      {
        cpp_typecheck_fargst fargs;

        exprt symbol_expr = resolve(
          to_cpp_name(
            static_cast<const irept &>(to_array_type(type).element_type())),
          cpp_typecheck_resolvet::wantt::BOTH,
          fargs);

        if(symbol_expr.id() != ID_type)
        {
          // _NOT_ a type
          index_exprt index_expr(symbol_expr, to_array_type(type).size());
          expr.copy_to_operands(index_expr);
          expr.remove(ID_type_arg);
        }
      }
    }
  }

  complete_type_operand(expr);
  throw_if_incomplete_dependency(expr);
  c_typecheck_baset::typecheck_expr_sizeof(expr);
}

/// N5008 [expr.sizeof]/1: the operand shall not be an incomplete class type.
/// When the class is a plain class that is only declared so far (not a
/// template specialization that failed to instantiate), the enclosing
/// instantiation may well succeed later in the translation unit
/// ([temp.point]): report it as an incomplete_dependency_exceptiont, which
/// typecheck_compound_type turns into "instantiate again later".
void cpp_typecheckt::throw_if_incomplete_dependency(const exprt &expr)
{
  const typet *t = nullptr;
  if(!expr.operands().empty())
    t = &to_unary_expr(expr).op().type();
  else if(expr.find(ID_type_arg).is_not_nil())
    t = static_cast<const typet *>(&expr.find(ID_type_arg));
  else
    return;
  while(t->id() == ID_array || t->id() == ID_already_typechecked)
  {
    t = t->id() == ID_array ? &to_array_type(*t).element_type()
                            : &to_type_with_subtype(*t).subtype();
  }
  if(t->id() != ID_struct_tag && t->id() != ID_union_tag)
    return;
  const symbolt *s = symbol_table.lookup(to_tag_type(*t).get_identifier());
  if(
    s == nullptr || (s->type.id() != ID_struct && s->type.id() != ID_union) ||
    !to_struct_union_type(s->type).is_incomplete() ||
    s->type.get_bool(ID_template_class_instance))
  {
    return;
  }
  // Not reported: the instantiation is retried where the complete type is
  // required; if the class is never defined, that use reports the error.
  throw incomplete_dependency_exceptiont{};
}

/// N5008 [expr.sizeof]/1, [expr.alignof]/1: the operand type must be complete,
/// and [temp.inst]/2: a class template specialization is implicitly
/// instantiated when the completeness of the class type affects the semantics
/// of the program.  A specialization named only through a typedef/alias
/// (whose elaboration convert_non_template_declaration defers to first use)
/// is therefore elaborated here; without this `sizeof(alias_t)` reported an
/// incomplete type when the alias was the only mention of the instance.
/// A struct VALUE must have one operand per component of its type -- data
/// members AND the padding components inserted by the layout (add_padding),
/// in the type's order.  Sites that assemble a struct value from per-member
/// values start from this all-zero value and overwrite the members they set
/// (set_struct_member_value); the padding stays zero.  Building the value
/// from the data members alone (which the C++ front end used to do) left it
/// short by the padding components: goto conversion / symex then paired
/// operands with the wrong components or aborted
/// (`assign_from_struct: rhs.operands().size() == components.size()').
/// \return the zero value, or nothing when the type cannot be zero-initialised
///   (an incomplete or dependent member type)
std::optional<struct_exprt> cpp_typecheckt::zero_struct_value(
  const typet &type,
  const source_locationt &loc)
{
  const namespacet ns(symbol_table);
  const auto zero = itanium_abi_cpp_zero_initializer(type, loc, ns);
  if(!zero.has_value() || zero->id() != ID_struct)
    return {};
  return to_struct_expr(*zero);
}

/// Overwrite the operand of \p value that corresponds to \p component (a
/// component of \p struct_type, the followed type of value.type()).
void cpp_typecheckt::set_struct_member_value(
  struct_exprt &value,
  const struct_typet &struct_type,
  const struct_union_typet::componentt &component,
  exprt member_value)
{
  // Operands correspond to the components that are not methods, member
  // types or static members (see zero_initializer's struct case).
  std::size_t i = 0;
  for(const auto &c : struct_type.components())
  {
    if(
      c.type().id() == ID_code || c.get_bool(ID_is_type) ||
      c.get_bool(ID_is_static))
      continue;
    if(c.get_name() == component.get_name())
    {
      PRECONDITION(i < value.operands().size());
      value.operands()[i] = std::move(member_value);
      return;
    }
    ++i;
  }
  UNREACHABLE;
}

void cpp_typecheckt::complete_type_operand(exprt &expr)
{
  if(!expr.operands().empty() || expr.find(ID_type_arg).is_nil())
    return;
  typet &type_arg = static_cast<typet &>(expr.add(ID_type_arg));
  typecheck_type(type_arg);
  const typet *t = &type_arg;
  while(t->id() == ID_array)
    t = &to_array_type(*t).element_type();
  elaborate_class_template(*t);
  already_typechecked_typet::make_already_typechecked(type_arg);
}

void cpp_typecheckt::typecheck_expr_alignof(exprt &expr)
{
  // GNU __alignof__(expression): the C++ grammar only has the
  // type-id form (N5008 [expr.alignof]; the expression operand is the
  // GNU extension), so the parser parses the parenthesised operand as
  // a type-id -- a name that actually denotes an object mis-parses as
  // a type and resolution with wantt::TYPE failed ("found no match
  // for symbol ..."), which in an alignment-specifier position
  // (libstdc++'s __aligned_membuf: `alignas(__alignof__(_M_t))`)
  // silently degraded the alignment to 1.  Disambiguate exactly like
  // typecheck_expr_sizeof above.
  if(expr.operands().empty())
  {
    const typet &type = static_cast<const typet &>(expr.find(ID_type_arg));

    if(type.id() == ID_cpp_name)
    {
      cpp_typecheck_fargst fargs;

      exprt symbol_expr = resolve(
        to_cpp_name(static_cast<const irept &>(type)),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      if(symbol_expr.id() != ID_type)
      {
        expr.copy_to_operands(symbol_expr);
        expr.remove(ID_type_arg);
      }
    }
  }

  complete_type_operand(expr);
  c_typecheck_baset::typecheck_expr_alignof(expr);
}

void cpp_typecheckt::typecheck_expr_ptrmember(exprt &expr)
{
  typecheck_expr_ptrmember(expr, cpp_typecheck_fargst());
}

void cpp_typecheckt::typecheck_function_expr(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.id() == ID_cpp_name)
    typecheck_expr_cpp_name(expr, fargs);
  else if(expr.id() == ID_member)
  {
    typecheck_expr_operands(expr);
    typecheck_expr_member(expr, fargs);
  }
  else if(expr.id() == ID_ptrmember)
  {
    typecheck_expr_operands(expr);
    add_implicit_dereference(to_unary_expr(expr).op());

    // is operator-> overloaded?
    if(to_unary_expr(expr).op().type().id() != ID_pointer)
    {
      std::string op_name = "operator->";

      const cpp_namet cpp_name(op_name, expr.source_location());

      // Build as a member function call: obj.operator->()
      exprt member(ID_member);
      member.add(ID_component_cpp_name) = cpp_name;
      member.copy_to_operands(
        already_typechecked_exprt{to_unary_expr(expr).op()});

      side_effect_expr_function_callt function_call(
        std::move(member), {}, uninitialized_typet{}, expr.source_location());

      typecheck_side_effect_function_call(function_call);

      add_implicit_dereference(function_call);
      already_typechecked_exprt::make_already_typechecked(function_call);

      to_unary_expr(expr).op().swap(function_call);
      typecheck_function_expr(expr, fargs);
      return;
    }

    typecheck_expr_ptrmember(expr, fargs);
  }
  else
    typecheck_expr(expr);
}

bool cpp_typecheckt::overloadable(const exprt &expr)
{
  // at least one argument must have class or enumerated type

  for(const auto &op : expr.operands())
  {
    typet t = op.type();

    if(is_reference(t))
      t = to_reference_type(t).base_type();

    if(
      t.id() == ID_struct || t.id() == ID_union || t.id() == ID_c_enum ||
      t.id() == ID_c_enum_tag || t.id() == ID_struct_tag ||
      t.id() == ID_union_tag)
    {
      return true;
    }
  }

  return false;
}

struct operator_entryt
{
  const irep_idt id;
  const char *op_name;
} const operators[] = {
  {ID_plus, "+"},        {ID_minus, "-"},       {ID_mult, "*"},
  {ID_div, "/"},         {ID_mod, "%"},         {ID_bitnot, "~"},
  {ID_bitand, "&"},      {ID_bitor, "|"},       {ID_bitxor, "^"},
  {ID_not, "!"},         {ID_unary_minus, "-"}, {ID_and, "&&"},
  {ID_or, "||"},         {ID_not, "!"},         {ID_index, "[]"},
  {ID_equal, "=="},      {ID_lt, "<"},          {ID_le, "<="},
  {ID_gt, ">"},          {ID_ge, ">="},         {ID_spaceship, "<=>"},
  {ID_shl, "<<"},        {ID_shr, ">>"},        {ID_notequal, "!="},
  {ID_dereference, "*"}, {ID_ptrmember, "->"},  {irep_idt(), nullptr}};

/// N5008 [over.match.oper]/3.4 (C++20): the rewritten and reversed
/// candidates of a comparison `x @ y' -- `(x <=> y) @ 0', `0 @ (y <=> x)',
/// `!(x == y)', `y == x'.  Rewrites \p expr into the selected candidate and
/// returns true; leaves it alone and returns false when there is none.
bool cpp_typecheckt::rewritten_comparison_candidate(exprt &expr)
{
  // N5008 [over.match.oper]/3.4 (C++20): for a relational operator `x @ y'
  // the candidate set includes the REWRITTEN candidates `(x <=> y) @ 0' and
  // the reversed `0 @ (y <=> x)'; for `x != y' the rewritten `!(x == y)' and
  // the reversed `!(y == x)'; for `x == y' the reversed `y == x'.  The
  // operator<=> / operator== may be a member or a non-member (friend or
  // namespace-scope, found by ADL) -- libstdc++'s std::pair declares both as
  // namespace-scope templates, and the requires-expressions of
  // three_way_comparable_with (`__t < __u') test exactly these rewrites.
  // Previously only a member operator<=> was tried and the synthesized
  // comparison against 0 was left un-type-checked ("warning: ignoring <").
  const auto is_class_type = [](const typet &t)
  {
    const typet &u = is_reference(t) ? to_reference_type(t).base_type() : t;
    return u.id() == ID_struct_tag || u.id() == ID_struct;
  };
  // [over.match.oper]/3.3: with no operand of class type only candidates
  // taking the operands' enumeration types remain -- the rewrite below
  // does not model that restriction, so it is limited to class operands.
  if(
    (expr.id() == ID_lt || expr.id() == ID_gt || expr.id() == ID_le ||
     expr.id() == ID_ge || expr.id() == ID_equal || expr.id() == ID_notequal) &&
    expr.operands().size() == 2 &&
    (is_class_type(to_binary_expr(expr).op0().type()) ||
     is_class_type(to_binary_expr(expr).op1().type())))
  {
    const source_locationt loc = expr.source_location();
    const exprt &x = to_binary_expr(expr).op0();
    const exprt &y = to_binary_expr(expr).op1();

    // the call `a OP b' to a user-declared operator OP (member, then
    // non-member with ADL), or nothing when there is none
    auto rewritten_call = [&](
                            const std::string &op_name,
                            const exprt &a,
                            const exprt &b) -> std::optional<exprt>
    {
      const cpp_namet name(op_name, loc);
      const typet a_type = is_reference(a.type())
                             ? to_reference_type(a.type()).base_type()
                             : a.type();
      if(a_type.id() == ID_struct_tag || a_type.id() == ID_struct)
      {
        exprt member(ID_member);
        member.add(ID_component_cpp_name) = name;
        member.copy_to_operands(already_typechecked_exprt{a});
        side_effect_expr_function_callt call(
          std::move(member), {}, uninitialized_typet{}, loc);
        call.arguments().push_back(b);
        try
        {
          sfinae_contextt sfinae_guard{*this};
          typecheck_side_effect_function_call(call);
          return std::move(call);
        }
        catch(...)
        {
        }
      }
      side_effect_expr_function_callt call(
        name.as_expr(), {}, uninitialized_typet{}, loc);
      call.arguments().push_back(a);
      call.arguments().push_back(b);
      try
      {
        sfinae_contextt sfinae_guard{*this};
        typecheck_side_effect_function_call(call);
        return std::move(call);
      }
      catch(...)
      {
      }
      return {};
    };

    if(expr.id() == ID_equal || expr.id() == ID_notequal)
    {
      // `x == y' has been tried by the lookup above; `x != y' is rewritten
      // to `!(x == y)', and both are tried reversed
      std::optional<exprt> eq;
      if(expr.id() == ID_notequal)
        eq = rewritten_call("operator==", x, y);
      if(!eq.has_value())
        eq = rewritten_call("operator==", y, x);
      if(eq.has_value())
      {
        exprt result = typecast_exprt::conditional_cast(*eq, bool_typet());
        if(expr.id() == ID_notequal)
          result = not_exprt(result);
        result.add_source_location() = loc;
        expr.swap(result);
        return true;
      }
    }
    else
    {
      std::optional<exprt> cmp = rewritten_call("operator<=>", x, y);
      irep_idt relation = expr.id();
      if(!cmp.has_value())
      {
        cmp = rewritten_call("operator<=>", y, x);
        // `0 @ (y <=> x)' is `(y <=> x) @' 0' with the converse relation
        if(relation == ID_lt)
          relation = ID_gt;
        else if(relation == ID_gt)
          relation = ID_lt;
        else if(relation == ID_le)
          relation = ID_ge;
        else if(relation == ID_ge)
          relation = ID_le;
      }
      if(cmp.has_value())
      {
        // `(x <=> y) @ 0': the comparison-category type's own operator@
        // against a literal 0 ([cmp.categories.pre]/3)
        exprt rel(relation, typet{});
        rel.add_to_operands(
          already_typechecked_exprt{*cmp}, from_integer(0, signed_int_type()));
        rel.add_source_location() = loc;
        typecheck_expr(rel);
        expr.swap(rel);
        return true;
      }
    }
  }

  return false;
}

/// N5008 [over.match.best]/2.1, [over.match.oper]/3: whether the non-member
/// operator function \p nonmember is a better candidate for the operands
/// \p operands than the member operator function \p member, whose implicit
/// object parameter takes the first operand ([over.match.funcs]/4): each
/// conversion sequence of \p nonmember is not worse ([over.ics.rank]) and
/// one is better.  Ranks come from implicit_conversion_sequence.
bool cpp_typecheckt::nonmember_operator_is_better(
  const exprt::operandst &operands,
  const irep_idt &member,
  const irep_idt &nonmember)
{
  const symbolt *member_symbol = symbol_table.lookup(member);
  const symbolt *nonmember_symbol = symbol_table.lookup(nonmember);
  if(
    member_symbol == nullptr || nonmember_symbol == nullptr ||
    member_symbol->type.id() != ID_code ||
    nonmember_symbol->type.id() != ID_code)
  {
    return false;
  }
  const auto &member_parameters =
    to_code_type(member_symbol->type).parameters();
  const auto &nonmember_parameters =
    to_code_type(nonmember_symbol->type).parameters();
  if(
    member_parameters.size() != operands.size() ||
    nonmember_parameters.size() != operands.size() ||
    member_parameters.front().get_this() == false ||
    member_parameters.front().type().id() != ID_pointer)
  {
    return false;
  }
  sfinae_contextt sfinae_guard{*this};
  bool better = false;
  bool worse = false;
  for(std::size_t i = 0; i < operands.size() && !worse; ++i)
  {
    // the implicit object parameter: reference to the class
    // ([over.match.funcs]/4)
    const typet member_type =
      i == 0 ? typet{reference_type(
                 to_pointer_type(member_parameters[0].type()).base_type())}
             : member_parameters[i].type();
    unsigned member_rank = 0;
    unsigned nonmember_rank = 0;
    bool member_ok = false;
    bool nonmember_ok = false;
    try
    {
      member_ok =
        implicit_conversion_sequence(operands[i], member_type, member_rank);
      nonmember_ok = implicit_conversion_sequence(
        operands[i], nonmember_parameters[i].type(), nonmember_rank);
    }
    catch(...)
    {
      member_ok = false;
    }
    if(!member_ok || !nonmember_ok)
      worse = true;
    else if(nonmember_rank > member_rank)
      worse = true;
    else if(nonmember_rank < member_rank)
      better = true;
  }
  return better && !worse;
}

bool cpp_typecheckt::operator_is_overloaded(exprt &expr)
{
  // Check argument types first.
  // At least one struct/enum operand is required.

  if(!overloadable(expr))
    return false;
  else if(expr.id() == ID_dereference && expr.get_bool(ID_C_implicit))
    return false;

  // N5008 [over.match.oper]/3, [temp.inst]/2: the operand classes' members
  // are looked up, so a class template specialization named so far only
  // through a typedef (`reverse_iterator' of a container) is instantiated
  // now.
  for(const auto &op : expr.operands())
  {
    const typet &t = is_reference(op.type())
                       ? to_reference_type(op.type()).base_type()
                       : op.type();
    if(t.id() == ID_struct_tag || t.id() == ID_union_tag)
      elaborate_class_template(t);
  }

  // Mark all resolutions below as operator-EXPRESSION candidate gathering
  // ([over.match.oper]/3) -- see operator_expr_lookup_depth.
  struct op_expr_guardt
  {
    unsigned &depth;
    explicit op_expr_guardt(unsigned &d) : depth(d)
    {
      ++depth;
    }
    ~op_expr_guardt()
    {
      --depth;
    }
  } op_expr_guard{operator_expr_lookup_depth};

  PRECONDITION(expr.operands().size() >= 1);

  if(expr.id() == "explicit-typecast")
  {
    // N5008 [expr.type.conv]/2: only a single-operand functional cast can
    // invoke a CONVERSION function; with two or more operands the
    // expression is direct-initialization and this branch does not apply.
    // A malformed cast (nil target type) cannot name a conversion function
    // either -- both shapes occur transiently while
    // guess_function_template_args substitutes into a candidate signature
    // (libc++'s views::take call), and to_unary_expr below would abort.
    if(expr.operands().size() != 1 || expr.type().is_nil())
      return false;

    // the cast operator can be overloaded

    typet t = expr.type();
    typecheck_type(t);
    std::string op_name =
      std::string("operator") + "(" + cpp_type2name(t) + ")";

    // turn this into a function call
    const cpp_namet cpp_name(op_name, expr.source_location());

    // See if the struct declares the cast operator as a member
    bool found_in_struct = false;
    PRECONDITION(!expr.operands().empty());
    const typet &t0 = to_unary_expr(expr).op().type();

    if(t0.id() == ID_struct_tag)
    {
      for(const auto &c : follow_tag(to_struct_tag_type(t0)).components())
      {
        if(!c.get_bool(ID_from_base) && c.get_base_name() == op_name)
        {
          found_in_struct = true;
          break;
        }
      }
    }

    if(!found_in_struct)
      return false;

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cpp_name;

    member.copy_to_operands(
      already_typechecked_exprt{to_unary_expr(expr).op()});

    side_effect_expr_function_callt function_call(
      std::move(member), {}, uninitialized_typet{}, expr.source_location());
    function_call.arguments().reserve(expr.operands().size());

    if(expr.operands().size() > 1)
    {
      for(exprt::operandst::const_iterator it = (expr.operands().begin() + 1);
          it != (expr).operands().end();
          it++)
        function_call.arguments().push_back(*it);
    }

    typecheck_side_effect_function_call(function_call);

    if(expr.id() == ID_ptrmember)
    {
      add_implicit_dereference(function_call);
      already_typechecked_exprt::make_already_typechecked(function_call);
      to_unary_expr(expr).op().swap(function_call);
      typecheck_expr(expr);
      return true;
    }

    expr.swap(function_call);
    return true;
  }

  for(const operator_entryt *e = operators; !e->id.empty(); e++)
  {
    if(expr.id() == e->id)
    {
      DATA_INVARIANT(
        expr.id() != ID_dereference || !expr.get_bool(ID_C_implicit),
        "no implicit dereference");

      std::string op_name = std::string("operator") + e->op_name;

      // first do function/operator
      const cpp_namet cpp_name(op_name, expr.source_location());

      // turn this into a function call
      // There are two options to overload an operator:
      //
      // 1. In the scope of a as a.operator(b, ...)
      // 2. Anywhere in scope as operator(a, b, ...)
      //
      // Using both is not allowed.
      //
      // We try and fail silently, maybe conversions will work
      // instead.

      // TODO: need to resolve an incomplete struct (template) here
      // go into scope of first operand.
      //
      // N5008 [over.match.oper]/3.2: the member candidate set for `a @ b` is
      // the qualified lookup of `T1::operator@`, where T1 is the type of the
      // left operand.  An lvalue of reference-to-class type (as produced by
      // e.g. `static_cast<std::ostream &>(x)`) is an lvalue of the referenced
      // class type and thus has that class's member operators as candidates,
      // but CBMC represents such an operand with a reference type rather than
      // the bare struct_tag -- strip a leading reference before deciding
      // whether the first operand has class type.
      typet op0_operator_type = to_multi_ary_expr(expr).op0().type();
      if(is_reference(op0_operator_type))
        op0_operator_type = to_reference_type(op0_operator_type).base_type();
      if(op0_operator_type.id() == ID_struct_tag)
      {
        const irep_idt &struct_identifier =
          op0_operator_type.get(ID_identifier);

        // [over.match.oper]/3.2: the SET OF MEMBER CANDIDATES is
        // the result of a qualified lookup of `T1::operator@`.
        // CBMC's `resolve` performs RECURSIVE name lookup that
        // walks parent scopes when no match is found in the struct
        // scope, so a free `operator@` declared at file scope
        // (e.g., `BigInt operator%(const BigInt &,
        // const BigInt &)` in `bigint.hh`) would be returned here
        // even though T1 (BigInt) does not declare it as a member.
        // The downstream synthesis of `a.operator@(b)` then
        // produces a malformed member-call and the 2nd-option
        // (free-function) path is never reached, surfacing as
        //   conversion from 'const struct BigInt' to 'struct BigInt':
        //   implicit arithmetic conversion not permitted
        // for any free `operator@` between two `BigInt` operands
        // when one of them has a corresponding `operator@=` member
        // (which is the typical ADT pattern).  Skip the 1st option
        // entirely if T1 does not declare the operator as a member.
        bool has_member_op = false;
        // True when the only member operator@ candidate is a function template
        // (no non-template member component matched): used to prefer a
        // non-member non-template operator@ before instantiating the member
        // template's body ([over.match.best]/2, [temp.inst]).
        bool member_has_template_op = false;
        const struct_typet &class_type =
          follow_tag(struct_tag_typet{struct_identifier});
        for(const auto &c : class_type.components())
        {
          // Inherited operators are member candidates too: the qualified
          // lookup of `T1::operator@` ([over.match.oper]/3.2) finds
          // members declared in base classes ([class.member.lookup]), so
          // from_base components must not be skipped.  A free operator
          // declared at file scope is not a component of T1, so this
          // still excludes the non-member case the gate guards against.
          if(c.get_base_name() == op_name && c.type().id() == ID_code)
          {
            has_member_op = true;
            break;
          }
        }

        // A member operator that is a function TEMPLATE is not stored as a
        // plain ID_code component; it lives in the class's scope.  N5008
        // [over.match.oper]/3.2 includes such template members in the member
        // candidate set (e.g. mstreamt's
        // `template <class T> mstreamt &operator<<(const T&)`), so detect them
        // with a scope-only lookup.  SCOPE_ONLY does not walk parent scopes, so
        // this still excludes file-scope free operators (the case the gate
        // guards against).  Also record whether any member candidate is a
        // function template: if so, a non-member non-template operator@ that is
        // a perfect match must be preferred *before* the member is resolved,
        // since resolving a member template instantiates its body.
        {
          cpp_scopet &member_scope = cpp_scopes.get_scope(struct_identifier);
          const auto member_ops =
            member_scope.lookup(op_name, cpp_scopet::SCOPE_ONLY);
          if(!member_ops.empty())
            has_member_op = true;
          for(const auto &id_ptr : member_ops)
          {
            const symbolt *s = symbol_table.lookup(id_ptr->identifier);
            if(s != nullptr && s->type.get_bool(ID_is_template))
            {
              member_has_template_op = true;
              break;
            }
          }
        }

        if(has_member_op)
        {
          // get that scope
          cpp_save_scopet save_scope(cpp_scopes);
          cpp_scopes.set_scope(struct_identifier);

          // If the only member operator@ candidate is a function template, a
          // non-member non-template operator@ that is an exact match for the
          // object argument must be preferred ([over.match.oper]/3,
          // [over.match.best]/2).  Decide this BEFORE resolving the member
          // candidate: resolving a member function template here instantiates
          // its body, and a type error in that body (for a T the template is
          // not meant to handle) would be emitted as a hard error even though
          // this candidate is ultimately not selected -- whereas only the
          // selected, odr-used specialization's body may be instantiated
          // ([temp.inst]/2,4, [basic.def.odr]).  Concretely, for messaget's
          //   template <class T> mstreamt &operator<<(const T &x)
          //     { static_cast<std::ostream &>(*this) << x; ... }
          // and the free `operator<<(mstreamt &, eomt)`, `m << eom` must pick
          // the free operator; instantiating the member template's body for
          // T=eomt otherwise fails with "operator 'shl' not defined".
          if(member_has_template_op)
          {
            save_scope.restore(); // leave struct scope for free/ADL lookup

            cpp_typecheck_fargst free_fargs;
            free_fargs.operands = expr.operands();
            free_fargs.has_object = false;
            free_fargs.in_use = true;
            const exprt free_resolve = resolve(
              cpp_name, cpp_typecheck_resolvet::wantt::VAR, free_fargs, false);

            bool prefer_free = false;
            if(free_resolve.is_not_nil() && free_resolve.id() == ID_symbol)
            {
              const symbolt *fsym = symbol_table.lookup(
                to_symbol_expr(free_resolve).get_identifier());
              if(
                fsym != nullptr && fsym->type.id() == ID_code &&
                fsym->type.find(irep_idt{"#fn_template_args"}).is_nil())
              {
                // non-template free operator: require a perfect (identity)
                // match on EVERY parameter, so any member candidate (which is
                // at best also a perfect match, in which case the program is
                // ambiguous anyway) is never wrongly overridden.  This is the
                // only case where preferring the free operator without ranking
                // the member is guaranteed correct.
                const auto &fparams = to_code_type(fsym->type).parameters();
                auto strip = [](typet t)
                {
                  if(
                    t.id() == ID_pointer && (t.get_bool(ID_C_reference) ||
                                             t.get_bool(ID_C_rvalue_reference)))
                    t = to_pointer_type(t).base_type();
                  t.remove(ID_C_constant);
                  return t;
                };
                if(fparams.size() == expr.operands().size())
                {
                  bool all_exact = true;
                  for(std::size_t i = 0; i < fparams.size(); ++i)
                  {
                    if(
                      strip(fparams[i].type()) !=
                      strip(expr.operands()[i].type()))
                    {
                      all_exact = false;
                      break;
                    }
                  }
                  prefer_free = all_exact;
                }
              }
            }

            if(prefer_free)
            {
              side_effect_expr_function_callt function_call(
                cpp_name.as_expr(),
                {},
                uninitialized_typet{},
                expr.source_location());
              function_call.arguments().reserve(expr.operands().size());
              for(const auto &op : as_const(expr).operands())
                function_call.arguments().push_back(op);
              typecheck_side_effect_function_call(function_call);
              expr = function_call;
              return true;
            }

            // free operator not preferred: re-enter the struct scope for the
            // member resolution below.
            cpp_scopes.set_scope(struct_identifier);
          }

          // build fargs for resolver
          cpp_typecheck_fargst fargs;
          fargs.operands = expr.operands();
          fargs.has_object = true;
          fargs.in_use = true;

          // should really be a qualified search.
          //
          // N5008 [over.match.oper]/3: the member and non-member operator@
          // candidates form ONE overload set.  If no *member* candidate is
          // viable for these operands, resolution must continue with the
          // non-member candidates -- it is not an error yet.  CBMC's resolve
          // throws (rather than returning nil) when the member scope declares
          // same-named candidates but none is viable for the given arguments;
          // catch that here so the non-member ("2nd option") path below is
          // still tried, instead of turning a member-candidate mismatch into a
          // hard "found no match"/built-in-shift error.  Surfaces for
          // `static_cast<std::ostream &>(x) << "literal"` inside mstreamt's
          // member operator<< template body: std::basic_ostream has member
          // operator<< overloads but none is viable for a `const char *`
          // argument, so the free operator<<(basic_ostream<C> &, const char *)
          // must be selected.
          exprt resolve_result = nil_exprt();
          try
          {
            resolve_result = resolve(
              cpp_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);
          }
          catch(int)
          {
            resolve_result = nil_exprt();
          }

          if(resolve_result.is_not_nil())
          {
            // Per N5008 [over.match.oper]/3 + [over.match.best]/2:
            // member and non-member candidates form ONE combined
            // overload set; when both have same-rank conversion
            // sequences, a non-template specialization is preferred
            // over a function template specialization.
            //
            // CBMC's previous behaviour returned the first viable
            // member candidate without consulting the non-member
            // (ADL/free) set.  When the member candidate is a
            // function-template instantiation and a non-template
            // free operator is also viable (typically a `friend`
            // operator declared in the enclosing class with the
            // exact same parameter types), the free one must win
            // per [over.match.best]/2.
            //
            // Visible symptom on CBMC's own source:
            //   class messaget {
            //   public:
            //     class mstreamt : public std::ostringstream {
            //       template <class T> mstreamt &
            //       operator<<(const T &x) {  // template member
            //         static_cast<std::ostream &>(*this) << x;
            //         return *this;
            //       }
            //     };
            //     class eomt {};
            //     friend mstreamt &operator<<(mstreamt &, eomt);
            //   };
            // For `m << eom` (eom: messaget::eomt), the friend
            // non-template should win over the member template.
            // CBMC instead instantiated the member template, whose
            // body's `static_cast<std::ostream &>(*this) << eomt`
            // then fails with "operator 'shl' not defined".
            //
            // Detect the case: if the member candidate is a
            // function-template instantiation
            // (`#fn_template_args` set on its type), also try the
            // non-member candidate; if the non-member is
            // non-template, prefer it.
            bool member_is_template_specialization = false;
            if(resolve_result.id() == ID_symbol)
            {
              const symbolt *sym = symbol_table.lookup(
                to_symbol_expr(resolve_result).get_identifier());
              if(
                sym != nullptr &&
                sym->type.find(irep_idt{"#fn_template_args"}).is_not_nil())
              {
                member_is_template_specialization = true;
              }
            }
            if(member_is_template_specialization)
            {
              // Step out of the struct scope before doing the
              // non-member lookup so ADL-discovered candidates
              // (e.g., `friend operator@` declared in the
              // enclosing class) participate.
              save_scope.restore();

              cpp_typecheck_fargst free_fargs;
              free_fargs.operands = expr.operands();
              free_fargs.has_object = false;
              free_fargs.in_use = true;
              exprt free_resolve = resolve(
                cpp_name,
                cpp_typecheck_resolvet::wantt::VAR,
                free_fargs,
                false);
              if(free_resolve.is_not_nil())
              {
                bool free_is_non_template = true;
                // N5008 [over.match.best]/2: a non-template candidate is
                // preferred over a function-template specialization only when
                // their conversion sequences are otherwise indistinguishable.
                // Prefer the free operator over the member template only when
                // the free operator's object (first) parameter is an EXACT
                // match for the object argument's type.  If the free operator
                // would need a derived-to-base conversion for the object (e.g.
                // a free `operator<<(std::ostream&, ...)` on a
                // `messaget::mstreamt` that derives from ostream, versus the
                // member `mstreamt::operator<<` whose implicit object parameter
                // is an exact `mstreamt&`), the member has the strictly better
                // conversion sequence and must win -- otherwise the free
                // operator's `std::ostream&` result cannot be returned as the
                // derived `mstreamt&`.
                bool free_object_param_exact = false;
                if(free_resolve.id() == ID_symbol)
                {
                  const symbolt *fsym = symbol_table.lookup(
                    to_symbol_expr(free_resolve).get_identifier());
                  if(
                    fsym != nullptr &&
                    fsym->type.find(irep_idt{"#fn_template_args"}).is_not_nil())
                  {
                    free_is_non_template = false;
                  }
                  if(fsym != nullptr && fsym->type.id() == ID_code)
                  {
                    const auto &fparams = to_code_type(fsym->type).parameters();
                    if(!fparams.empty())
                    {
                      typet p0 = fparams.front().type();
                      if(
                        p0.id() == ID_pointer &&
                        (p0.get_bool(ID_C_reference) ||
                         p0.get_bool(ID_C_rvalue_reference)))
                        p0 = to_pointer_type(p0).base_type();
                      typet obj = to_multi_ary_expr(expr).op0().type();
                      if(
                        obj.id() == ID_pointer &&
                        (obj.get_bool(ID_C_reference) ||
                         obj.get_bool(ID_C_rvalue_reference)))
                        obj = to_pointer_type(obj).base_type();
                      if(
                        p0.id() == ID_struct_tag && obj.id() == ID_struct_tag &&
                        to_struct_tag_type(p0).get_identifier() ==
                          to_struct_tag_type(obj).get_identifier())
                        free_object_param_exact = true;
                    }
                  }
                }
                if(free_is_non_template && free_object_param_exact)
                {
                  side_effect_expr_function_callt function_call(
                    cpp_name.as_expr(),
                    {},
                    uninitialized_typet{},
                    expr.source_location());
                  function_call.arguments().reserve(expr.operands().size());
                  for(const auto &op : as_const(expr).operands())
                    function_call.arguments().push_back(op);
                  typecheck_side_effect_function_call(function_call);
                  if(expr.id() == ID_ptrmember)
                  {
                    add_implicit_dereference(function_call);
                    already_typechecked_exprt::make_already_typechecked(
                      function_call);
                    to_multi_ary_expr(expr).op0() = function_call;
                    typecheck_expr(expr);
                    return true;
                  }
                  expr = function_call;
                  return true;
                }
              }
              // Fall back: re-enter struct scope so the member
              // call below uses the right scope.
              cpp_scopes.set_scope(struct_identifier);
            }

            // N5008 [over.match.oper]/3, [over.match.best]/2.1: the member
            // and the non-member candidates are ranked together; a
            // non-member whose conversion sequences are all at least as
            // good, one of them better, wins over the member.
            // resolve returns the member function as `member' of the object
            const exprt &member_function =
              resolve_result.id() == ID_member
                ? static_cast<const exprt &>(resolve_result)
                : resolve_result;
            const irep_idt member_identifier =
              member_function.id() == ID_member
                ? member_function.get(ID_component_name)
                : member_function.get(ID_identifier);
            if(
              expr.id() != ID_ptrmember && !member_identifier.empty() &&
              !member_is_template_specialization)
            {
              save_scope.restore();
              cpp_typecheck_fargst free_fargs;
              free_fargs.operands = expr.operands();
              free_fargs.has_object = false;
              free_fargs.in_use = true;
              exprt free_resolve = nil_exprt{};
              try
              {
                sfinae_contextt sfinae_guard{*this};
                free_resolve = resolve(
                  cpp_name,
                  cpp_typecheck_resolvet::wantt::VAR,
                  free_fargs,
                  false);
              }
              catch(...)
              {
                free_resolve = nil_exprt{};
              }
              if(
                free_resolve.id() == ID_symbol &&
                nonmember_operator_is_better(
                  expr.operands(),
                  member_identifier,
                  to_symbol_expr(free_resolve).get_identifier()))
              {
                side_effect_expr_function_callt function_call(
                  cpp_name.as_expr(),
                  {},
                  uninitialized_typet{},
                  expr.source_location());
                function_call.arguments().reserve(expr.operands().size());
                for(const auto &op : as_const(expr).operands())
                  function_call.arguments().push_back(op);
                typecheck_side_effect_function_call(function_call);
                expr = function_call;
                return true;
              }
              cpp_scopes.set_scope(struct_identifier);
            }

            // Found! We turn op(a, b, ...) into a.op(b, ...)
            exprt member(ID_member);
            member.add(ID_component_cpp_name) = cpp_name;

            member.copy_to_operands(
              already_typechecked_exprt{to_multi_ary_expr(expr).op0()});

            side_effect_expr_function_callt function_call(
              std::move(member),
              {},
              uninitialized_typet{},
              expr.source_location());
            function_call.arguments().reserve(expr.operands().size());

            if(expr.operands().size() > 1)
            {
              // skip first
              for(exprt::operandst::const_iterator it =
                    expr.operands().begin() + 1;
                  it != expr.operands().end();
                  it++)
                function_call.arguments().push_back(*it);
            }

            typecheck_side_effect_function_call(function_call);

            if(expr.id() == ID_ptrmember)
            {
              add_implicit_dereference(function_call);
              already_typechecked_exprt::make_already_typechecked(
                function_call);
              to_multi_ary_expr(expr).op0().swap(function_call);
              // Leave operator->'s class scope before type-checking the
              // ensuing member access, so it is access-checked at the
              // actual point of use rather than from within the class
              // that defines operator->.
              save_scope.restore();
              typecheck_expr(expr);
              return true;
            }

            expr = function_call;

            return true;
          }
        } // end if(has_member_op)
      }

      // 2nd option!
      {
        cpp_typecheck_fargst fargs;
        fargs.operands = expr.operands();
        fargs.has_object = false;
        fargs.in_use = true;

        exprt resolve_result =
          resolve(cpp_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

        // [over.match.oper]/3.4 (last paragraph): if no operand
        // has class type, the non-member candidate set is
        // restricted to operators whose first parameter type is T1
        // (or reference-to-T1) when T1 is an enumeration type, or
        // whose second parameter type is T2 (or reference-to-T2)
        // when T2 is an enumeration type.  Without this, a free
        // operator on a class type whose constructors implicitly
        // accept arithmetic operands (e.g.,
        // `operator<<(const BigInt &, const BigInt &)` with
        // `BigInt(unsigned long)` and `BigInt(int)`) silently wins
        // over the built-in operator for an arithmetic operand
        // pair like `1UL << enum_const`.  The built-in candidate
        // (with at most an integral promotion) outranks the
        // user-defined one (which requires a user-defined
        // conversion sequence on each operand) per
        // [over.ics.rank]/2; CBMC's `operator_is_overloaded` does
        // not enumerate built-in candidates, so apply the
        // [over.match.oper]/3.4 restriction here as a filter.
        if(resolve_result.is_not_nil())
        {
          bool any_class_operand = false;
          for(const auto &op : expr.operands())
          {
            typet t = op.type();
            if(is_reference(t))
              t = to_reference_type(t).base_type();
            if(
              t.id() == ID_struct || t.id() == ID_struct_tag ||
              t.id() == ID_union || t.id() == ID_union_tag)
            {
              any_class_operand = true;
              break;
            }
          }
          if(!any_class_operand)
          {
            // Locate the resolved function's parameter types.
            const code_typet *fn_type = nullptr;
            if(resolve_result.type().id() == ID_code)
              fn_type = &to_code_type(resolve_result.type());
            if(fn_type != nullptr && fn_type->parameters().size() >= 1)
            {
              auto matches_enum_operand =
                [](const typet &param_type, const exprt &operand) -> bool
              {
                typet ot = operand.type();
                if(is_reference(ot))
                  ot = to_reference_type(ot).base_type();
                if(ot.id() != ID_c_enum && ot.id() != ID_c_enum_tag)
                  return false;
                typet pt = param_type;
                if(is_reference(pt))
                  pt = to_reference_type(pt).base_type();
                if(pt.id() != ot.id())
                  return false;
                if(
                  pt.id() == ID_c_enum_tag &&
                  to_c_enum_tag_type(pt).get_identifier() !=
                    to_c_enum_tag_type(ot).get_identifier())
                  return false;
                return true;
              };
              const auto &params = fn_type->parameters();
              const auto &ops = expr.operands();
              bool restriction_ok = false;
              if(!ops.empty() && params.size() >= 1)
              {
                if(matches_enum_operand(params[0].type(), ops[0]))
                  restriction_ok = true;
              }
              if(!restriction_ok && ops.size() >= 2 && params.size() >= 2)
              {
                if(matches_enum_operand(params[1].type(), ops[1]))
                  restriction_ok = true;
              }
              if(!restriction_ok)
                resolve_result.make_nil();
            }
          }
        }

        if(resolve_result.is_not_nil())
        {
          // found!
          side_effect_expr_function_callt function_call(
            cpp_name.as_expr(),
            {},
            uninitialized_typet{},
            expr.source_location());
          function_call.arguments().reserve(expr.operands().size());

          // now do arguments
          for(const auto &op : as_const(expr).operands())
            function_call.arguments().push_back(op);

          typecheck_side_effect_function_call(function_call);

          if(expr.id() == ID_ptrmember)
          {
            add_implicit_dereference(function_call);
            already_typechecked_exprt::make_already_typechecked(function_call);
            to_multi_ary_expr(expr).op0() = function_call;
            typecheck_expr(expr);
            return true;
          }

          expr = function_call;

          return true;
        }
      }
    }
  }

  if(rewritten_comparison_candidate(expr))
    return true;

  return false;
}

/// Phase 2 target-typet overload — drives [temp.deduct.funcaddr]/1
/// deduction forward when the target is a pointer-to-function and
/// the operand is a cpp_name.  Falls through to the no-target
/// implementation otherwise.
void cpp_typecheckt::typecheck_expr_address_of(
  exprt &expr,
  const target_typet &target)
{
  if(
    target.has_target() && expr.id() == ID_address_of &&
    expr.operands().size() == 1 && to_unary_expr(expr).op().id() == ID_cpp_name)
  {
    exprt deduced = deduce_funcaddr_against_target(expr, *target.get());
    if(deduced.is_not_nil())
    {
      expr.swap(deduced);
      return;
    }
  }

  typecheck_expr_address_of(expr);
}

void cpp_typecheckt::typecheck_expr_address_of(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "address_of expects one operand" << eom;
    throw 0;
  }

  exprt &op = to_address_of_expr(expr).op();

  // N5008 [expr.unary.op]/3 with [class.static.data]/4: the address of a
  // constexpr variable is the address of the object, not of its value
  // (which the resolver substitutes for a constexpr scalar)
  if(op.is_constant() && !op.get(ID_C_constexpr_object).empty())
  {
    symbolt *object = symbol_table.get_writeable(op.get(ID_C_constexpr_object));
    if(object != nullptr)
    {
      // [basic.def.odr]/4: taking the address odr-uses the variable, so it
      // is an object with static storage duration, initialized with its
      // value ([basic.start.static]/2) -- no longer a mere named constant
      object->is_macro = false;
      exprt symbol = cpp_symbol_expr(*object);
      symbol.add_source_location() = op.source_location();
      op = std::move(symbol);
    }
  }

  // Per [expr.unary.op]/3: if the operand is a reference, &E produces
  // the address of the referred object.  Implicitly dereference the
  // reference first so the subsequent lvalue check passes.
  if(is_reference(op.type()))
    add_implicit_dereference(op);

  // Per [conv.rval] + [class.temporary]: temporary materialization
  // converts a prvalue to a glvalue denoting a temporary object.  CBMC
  // represents such a materialized temporary as a `temporary_object`
  // side effect, which the front end binds to reference parameters by
  // taking its address (e.g. an rvalue argument bound to a `T&&`
  // parameter).  That object has storage, so its address may be taken.
  // The C base typecheck below does not know about `temporary_object`
  // and would reject it as a non-lvalue; this matters when an already-
  // typechecked call carrying such a binding is re-typechecked (as
  // `cpp_constructor` does for constructor operands).  Mark it as an
  // lvalue so the address-of typecheck is idempotent.
  if(
    op.id() == ID_side_effect && op.get(ID_statement) == ID_temporary_object &&
    !op.get_bool(ID_C_lvalue))
  {
    op.set(ID_C_lvalue, true);
  }

  if(!op.get_bool(ID_C_lvalue) && expr.type().id() == ID_code)
  {
    error().source_location = expr.source_location();
    error() << "expr not an lvalue" << eom;
    throw 0;
  }

  if(op.type().id() == ID_code)
  {
    // we take the address of the method.
    // Per N5008 [conv.func]/1 + [over.over]/1: in lvalue-to-rvalue
    // conversion of a function-typed lvalue, take its address.
    // The implementation here assumes the lvalue arrived as a
    // member-access expression (ID_member); when overload
    // resolution arrives via a synthesised user-defined
    // conversion sequence (e.g. lambda → `std::function`
    // construction), the operand may be a different shape.
    // Emit a graceful error instead of aborting on the
    // DATA_INVARIANT — the caller's catch block then drops the
    // problematic candidate and overload resolution can
    // continue or report a localized "no viable conversion".
    if(op.id() == ID_symbol)
    {
      // N5008 [conv.func]/1: an lvalue naming a FREE function converts
      // to a pointer to the function -- the shape of a function name
      // inside a nested braced-init-list whose aggregate element is a
      // function-pointer type (`{ID_not, assume_not}` in a
      // std::map<irep_idt, assume_function> initializer).
      address_of_exprt address(op, pointer_type(op.type()));
      address.set(ID_C_implicit, true);
      op.swap(address);
    }
    else if(op.id() == ID_member)
    {
      exprt symb = cpp_symbol_expr(lookup(op.get(ID_component_name)));
      address_of_exprt address(symb, pointer_type(symb.type()));
      address.set(ID_C_implicit, true);
      op.swap(address);
    }
    else
    {
      error().source_location = expr.source_location();
      error() << "address-of code requires a member expression "
              << "(operand id=" << op.id() << ")" << eom;
      throw 0;
    }
  }

  if(op.id() == ID_address_of && op.get_bool(ID_C_implicit))
  {
    // must be the address of a function
    code_typet &code_type =
      to_code_type(to_pointer_type(op.type()).base_type());

    code_typet::parameterst &args = code_type.parameters();
    if(!args.empty() && args.front().get_this())
    {
      // it's a pointer to member function.  N5008 [expr.unary.op]/3.1:
      // `&C::m' has type "pointer to member of class C' of type T" where C'
      // is the class m is a member of -- the class declaring it, whose
      // object `this' points to; for a function inherited from a base B
      // that is B, not the class named in the qualified-id (`&D::in' is
      // `int (B::*)(int) const', which converts to `int (D::*)(int)
      // const' by [conv.mem]/2).  The member name records the class the
      // component was copied into.
      typet member_class = struct_tag_typet{code_type.get(ID_C_member_name)};
      const typet &this_type = args.front().type();
      if(
        this_type.id() == ID_pointer &&
        to_pointer_type(this_type).base_type().id() == ID_struct_tag)
      {
        member_class = to_pointer_type(this_type).base_type();
        member_class.remove(ID_C_constant);
        member_class.remove(ID_C_volatile);
      }
      op.type().add(ID_to_member) = member_class;

      if(code_type.get_bool(ID_C_is_virtual))
      {
        error().source_location = expr.source_location();
        error() << "pointers to virtual methods"
                << " are currently not implemented" << eom;
        throw 0;
      }
    }
  }
  else if(op.id() == ID_ptrmember && to_unary_expr(op).op().id() == "cpp-this")
  {
    // N5008 [expr.unary.op]/3.1: `&C::m' for a non-static data member m has
    // type "pointer to member of C of type T" and designates C::m.
    // [basic.compound]/3: a pointer to data member identifies the member
    // within any object of its class; the Itanium C++ ABI (section 2.3)
    // represents it by the member's offset in C, a ptrdiff_t-sized value,
    // and the null member pointer value ([conv.mem]/1) by -1.  By default the
    // front end adds data_member_pointer_bias() (a back-end workaround, see
    // itanium_abi_cpp_zero_initializer.h).
    const struct_tag_typet class_tag = to_struct_tag_type(
      to_pointer_type(to_unary_expr(op).op().type()).base_type());
    pointer_typet result_type = pointer_type(op.type());
    result_type.add(ID_to_member) = class_tag;
    if(op.type().id() == ID_c_bit_field)
    {
      // [class.bit]/3: `&' shall not be applied to a bit-field
      error().source_location = expr.source_location();
      error() << "cannot form a pointer to the bit-field member '"
              << op.get(ID_component_name) << "'" << eom;
      throw 0;
    }
    const auto offset =
      member_offset(follow_tag(class_tag), op.get(ID_component_name), *this);
    if(!offset.has_value())
    {
      error().source_location = expr.source_location();
      error() << "cannot determine the offset of member '"
              << op.get(ID_component_name) << "' of '" << to_string(class_tag)
              << "'" << eom;
      throw 0;
    }
    exprt value = typecast_exprt{
      from_integer(*offset + data_member_pointer_bias(), signed_size_type()),
      result_type};
    value.add_source_location() = expr.source_location();
    expr.swap(value);
    return;
  }

  // the C front end does not know about references
  const bool is_ref = is_reference(expr.type());
  c_typecheck_baset::typecheck_expr_address_of(expr);
  if(is_ref)
    expr.type() = reference_type(to_pointer_type(expr.type()).base_type());
}

void cpp_typecheckt::typecheck_expr_throw(exprt &expr)
{
  expr.type() = void_type();

  PRECONDITION(expr.operands().size() == 1 || expr.operands().empty());

  if(expr.operands().size() == 1)
  {
    // nothing really to do; one can throw _almost_ anything
    const typet &exception_type = to_unary_expr(expr).op().type();

    if(exception_type.id() == ID_empty)
    {
      error().source_location = to_unary_expr(expr).op().find_source_location();
      error() << "cannot throw void" << eom;
      throw 0;
    }

    // annotate the relevant exception IDs
    expr.set(ID_exception_list, cpp_exception_list(exception_type, *this));
  }
}

void cpp_typecheckt::typecheck_expr_new(exprt &expr)
{
  // next, find out if we do an array

  if(expr.type().id() == ID_array)
  {
    // first typecheck the element type
    typecheck_type(to_array_type(expr.type()).element_type());

    // typecheck the size
    exprt &size = to_array_type(expr.type()).size();
    typecheck_expr(size);

    bool size_is_unsigned = (size.type().id() == ID_unsignedbv);
    bitvector_typet integer_type(
      size_is_unsigned ? ID_unsignedbv : ID_signedbv, config.ansi_c.int_width);
    implicit_typecast(size, integer_type);

    expr.set(ID_statement, ID_cpp_new_array);

    // save the size expression
    expr.set(ID_size, to_array_type(expr.type()).size());

    // new actually returns a pointer, not an array
    pointer_typet ptr_type =
      pointer_type(to_array_type(expr.type()).element_type());
    expr.type().swap(ptr_type);
  }
  else
  {
    // first typecheck type
    typecheck_type(expr.type());

    expr.set(ID_statement, ID_cpp_new);

    pointer_typet ptr_type = pointer_type(expr.type());
    expr.type().swap(ptr_type);
  }

  exprt object_expr(ID_new_object, to_pointer_type(expr.type()).base_type());
  object_expr.set(ID_C_lvalue, true);

  already_typechecked_exprt::make_already_typechecked(object_expr);

  // not yet typechecked-stuff
  exprt &initializer = static_cast<exprt &>(expr.add(ID_initializer));

  // N5008 [expr.new]/24, [dcl.init.aggr]/4-5: `new T[n]{e1, ..., ek}'
  // aggregate-initializes the array: element i is copy-initialized from
  // e_i, the remaining elements are value-initialized (as for `new
  // T[n]{}').  Keep one initializer per listed element (#element_
  // initializers, applied by goto conversion before the per-element loop
  // over the others).  [dcl.init.general]/16.5 (C++20): a parenthesized
  // expression-list `new T[n](e1, ..., ek)' initializes the elements in the
  // same way; before C++20 it is ill-formed ([expr.new]/24).
  if(
    !initializer.operands().empty() &&
    expr.get(ID_statement) == ID_cpp_new_array)
  {
    if(
      initializer.id() != ID_initializer_list &&
      config.cpp.cpp_standard < configt::cppt::cpp_standardt::CPP20)
    {
      error().source_location = expr.find_source_location();
      error() << "new with array type and parenthesized initializer requires "
                 "C++20"
              << eom;
      throw 0;
    }
    irept &element_initializers = expr.add("#element_initializers");
    for(const auto &element : initializer.operands())
    {
      exprt element_object(
        ID_new_object, to_pointer_type(expr.type()).base_type());
      element_object.set(ID_C_lvalue, true);
      already_typechecked_exprt::make_already_typechecked(element_object);
      auto element_code = cpp_constructor(
        element.find_source_location(), element_object, {element});
      element_initializers.get_sub().push_back(
        element_code.has_value() ? static_cast<const irept &>(*element_code)
                                 : static_cast<const irept &>(code_skipt{}));
    }
    // the others are value-initialized
    initializer.operands().clear();
  }

  // For a default-initialized new-expression (no initializer arguments),
  // the selected default constructor must be accessible at the point of
  // the new-expression ([expr.new], [class.access]); cpp_constructor
  // resolves it in the object's own class scope, so check here from the
  // enclosing scope.
  if(initializer.operands().empty())
    check_default_constructor_access(
      to_pointer_type(expr.type()).base_type(),
      expr.find_source_location(),
      &cpp_scopes.current_scope());

  // N5008 [expr.new]/23 + [dcl.init.list]/3: `new T{...}' is
  // direct-list-initialization; [over.match.list]/1 phase 1 tries the
  // initializer-list constructors with the whole list as the argument,
  // phase 2 the elements (the parenthesised form's operands).
  exprt::operandst new_args = initializer.operands();
  if(
    initializer.id() == ID_initializer_list && !new_args.empty() &&
    has_viable_init_list_constructor(
      to_pointer_type(expr.type()).base_type(), initializer))
  {
    auto il_val = build_init_list_argument(
      to_pointer_type(expr.type()).base_type(), initializer);
    if(il_val.has_value())
    {
      already_typechecked_exprt::make_already_typechecked(*il_val);
      new_args.clear();
      new_args.push_back(std::move(*il_val));
    }
  }

  // N5008 [expr.new]/24 + [dcl.init.list]/3.4: `new T{e...}' with T an
  // aggregate aggregate-initializes the object ([dcl.init.aggr]) -- also for
  // a single element, which cpp_constructor would take as a conversion of
  // that element to T (`new node{3}')
  std::optional<codet> code;
  if(
    initializer.id() == ID_initializer_list && new_args.size() == 1 &&
    new_args.front().id() != ID_initializer_list &&
    expr.get(ID_statement) == ID_cpp_new &&
    to_pointer_type(expr.type()).base_type().id() == ID_struct_tag)
  {
    exprt list = initializer;
    auto aggregate_value = braced_return_aggregate_value(
      to_pointer_type(expr.type()).base_type(), list);
    if(aggregate_value.has_value())
    {
      if(aggregate_value->id() == ID_already_typechecked)
        aggregate_value = to_unary_expr(*aggregate_value).op();
      exprt target(ID_new_object, to_pointer_type(expr.type()).base_type());
      target.set(ID_C_lvalue, true);
      code = code_expressiont{side_effect_expr_assignt{
        std::move(target),
        *aggregate_value,
        to_pointer_type(expr.type()).base_type(),
        expr.find_source_location()}};
    }
  }
  if(!code.has_value())
    code = cpp_constructor(expr.find_source_location(), object_expr, new_args);

  // N5008 [expr.new]/17: a new-initializer that is an EMPTY pair of
  // parentheses value-initializes the object ([dcl.init.general]/9); for
  // a scalar or a class without a user-provided default constructor that
  // means zero-initialization first.  A new-expression WITHOUT any
  // new-initializer default-initializes instead (indeterminate for a
  // scalar).  Both leave the operand list empty; the parser marks the
  // parenthesised form (#value_initialization).  cpp_constructor's POD
  // path treats both as default-initialization, so `::new(p) int()` (the
  // shape std::construct_at takes with no arguments) left the storage
  // unchanged.  Emit the zero-initialization here, ahead of whatever
  // cpp_constructor produced (default member initializers, which
  // [dcl.init.general]/9.2 applies after zero-initialization).
  // The same for a class whose default constructor is not user-provided
  // ([dcl.init.general]/9.1: zero-initialized, then default-initialized).
  // `new T{}' value-initializes as well ([dcl.init.list]/3.5).  For
  // `new T[n]()' / `new T[n]{}' each element is value-initialized
  // ([dcl.init.general]/9.3, [dcl.init.aggr]/5); the initializer built
  // here is applied to each element (cpp_new_initializer).
  const typet &new_object_type = to_pointer_type(expr.type()).base_type();
  if(
    (initializer.get_bool(ID_C_value_initialization) ||
     initializer.id() == ID_initializer_list) &&
    initializer.operands().empty() &&
    value_initialization_zero_initializes(new_object_type))
  {
    const auto zero = itanium_abi_cpp_zero_initializer(
      new_object_type, expr.find_source_location(), *this);
    if(zero.has_value())
    {
      exprt zero_target(ID_new_object, new_object_type);
      zero_target.set(ID_C_lvalue, true);
      side_effect_expr_assignt zero_assign{
        std::move(zero_target),
        zero.value(),
        new_object_type,
        expr.find_source_location()};
      code_blockt value_init;
      value_init.add(code_expressiont{std::move(zero_assign)});
      if(code.has_value())
        value_init.add(std::move(code.value()));
      code = std::move(value_init);
    }
  }

  if(code.has_value())
    expr.add(ID_initializer).swap(code.value());
  else
    expr.add(ID_initializer) = nil_exprt();

  // we add the size of the object for convenience of the
  // runtime library
  auto size_of_opt =
    size_of_expr(to_pointer_type(expr.type()).base_type(), *this);

  if(size_of_opt.has_value())
  {
    auto &sizeof_expr = static_cast<exprt &>(expr.add(ID_sizeof));
    sizeof_expr = size_of_opt.value();
    sizeof_expr.add(ID_C_c_sizeof_type) =
      to_pointer_type(expr.type()).base_type();
  }
}

static exprt collect_comma_expression(const exprt &src)
{
  exprt result;

  if(src.id() == ID_comma)
  {
    PRECONDITION(src.operands().size() == 2);
    result = collect_comma_expression(to_binary_expr(src).op0());
    result.copy_to_operands(to_binary_expr(src).op1());
  }
  else
    result.copy_to_operands(src);

  return result;
}

void cpp_typecheckt::typecheck_expr_explicit_typecast(exprt &expr)
{
  // C++23 auto(x) decay copy: replace with the operand
  if(expr.type().id() == ID_auto && expr.operands().size() == 1)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr(op);
    exprt result = op;
    expr.swap(result);
    return;
  }

  // these can have 0 or 1 arguments

  if(expr.operands().empty())
  {
    // Default value, e.g., int()
    typecheck_type(expr.type());

    // N5008 [expr.type.conv]/2: "if the type is cv void and the initializer
    // is () or {} (after pack expansion, if any), the expression is a prvalue
    // of type void that performs no initialization" -- `return void();' in
    // libc++'s __get_comp_type.  There is nothing to zero-initialize (the
    // attempt failed with "cannot zero-initialize 'void'").
    if(expr.type().id() == ID_empty)
    {
      exprt result =
        typecast_exprt{from_integer(0, signed_int_type()), empty_typet{}};
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }

    // N5008 [expr.type.conv]/2 + [dcl.init.general]/9.1: `T()' for a class
    // type VALUE-INITIALIZES the temporary -- zero-initialized and then, if
    // T's default constructor is non-trivial, default-initialized.  A
    // default member initializer makes the implicit default constructor
    // non-trivial ([class.default.ctor]/3), so `struct S { int v = 3; }; S()'
    // has v == 3; the plain zero value below gave 0 (the class is a POD to
    // the front end, and the constructor-call form was not taken).  Build
    // the temporary through the constructor path, which runs the
    // synthesized default constructor over the zero-initialized object.
    if(
      (expr.type().id() == ID_struct_tag || expr.type().id() == ID_union_tag) &&
      has_default_member_initializer(expr.type()))
    {
      exprt::operandst no_operands;
      exprt temporary;
      new_temporary(
        expr.source_location(), expr.type(), no_operands, temporary);
      // the zero-initialization that precedes the default-initialization
      // (members without a default member initializer are zero, not
      // indeterminate: `struct R { int v = 3; int w; }; R().w == 0')
      const auto zero = itanium_abi_cpp_zero_initializer(
        expr.type(), expr.find_source_location(), *this);
      if(zero.has_value() && temporary.find(ID_initializer).is_not_nil())
      {
        exprt new_object(ID_new_object);
        new_object.add_source_location() = expr.source_location();
        new_object.set(ID_C_lvalue, true);
        new_object.type() = expr.type();
        code_frontend_assignt zero_assign{new_object, *zero};
        zero_assign.add_source_location() = expr.source_location();
        code_blockt initializer;
        initializer.add(std::move(zero_assign));
        initializer.add(
          to_code(static_cast<const exprt &>(temporary.find(ID_initializer))));
        temporary.add(ID_initializer) = initializer;
      }
      expr.swap(temporary);
      return;
    }

    auto new_expr = itanium_abi_cpp_zero_initializer(
      expr.type(), expr.find_source_location(), *this);
    if(!new_expr.has_value())
    {
      error().source_location = expr.find_source_location();
      error() << "cannot zero-initialize '" << to_string(expr.type()) << "'"
              << eom;
      throw 0;
    }

    new_expr->add_source_location() = expr.source_location();

    // N5008 [expr.type.conv]/2 + [class.temporary]/2: `T()' for a class
    // type is a prvalue whose temporary is materialised when a member is
    // accessed (`B().g()', `T().m').  A bare struct constant has no object
    // to bind the implicit object parameter to ("found no match for symbol
    // 'g'"); produce the same compound literal the one-operand and braced
    // forms produce, which the member-access code knows how to address.
    if(expr.type().id() == ID_struct_tag || expr.type().id() == ID_union_tag)
    {
      exprt tmp(ID_compound_literal, expr.type());
      tmp.add_to_operands(std::move(*new_expr));
      tmp.add_source_location() = expr.source_location();
      tmp.set(ID_C_lvalue, true);
      expr = std::move(tmp);
    }
    else
      expr = *new_expr;
  }
  else if(expr.operands().size() == 1)
  {
    auto &op = to_unary_expr(expr).op();

    // Explicitly given value, e.g., int(1).
    // There is an expr-vs-type ambiguity, as it is possible to write
    // (f)(1), where 'f' is a function symbol and not a type.
    // This also exists with a "comma expression", e.g.,
    // (f)(1, 2, 3)

    if(expr.type().id() == ID_cpp_name)
    {
      // try to resolve as type
      cpp_typecheck_fargst fargs;

      exprt symbol_expr = resolve(
        to_cpp_name(static_cast<const irept &>(expr.type())),
        cpp_typecheck_resolvet::wantt::TYPE,
        fargs,
        false); // fail silently

      if(symbol_expr.id() == ID_type)
        expr.type() = symbol_expr.type();
      else
      {
        // It's really a function call. Note that multiple arguments
        // become a comma expression, and that these are already typechecked.
        side_effect_expr_function_callt f_call(
          static_cast<const exprt &>(static_cast<const irept &>(expr.type())),
          collect_comma_expression(op).operands(),
          uninitialized_typet{},
          expr.source_location());

        typecheck_side_effect_function_call(f_call);

        expr.swap(f_call);
        return;
      }
    }
    else
      typecheck_type(expr.type());

    // We allow (TYPE){ initializer_list }
    // This is called "compound literal", and is syntactic
    // sugar for a (possibly local) declaration.
    if(op.id() == ID_initializer_list)
    {
      // C++17: direct-list-initialization of scalar/enum types
      // e.g., byte{42} where byte is a scoped enum
      if(
        op.operands().size() == 1 &&
        (expr.type().id() == ID_c_enum_tag || expr.type().id() == ID_signedbv ||
         expr.type().id() == ID_unsignedbv || expr.type().id() == ID_c_bool ||
         expr.type().id() == ID_bool || expr.type().id() == ID_floatbv ||
         expr.type().id() == ID_pointer))
      {
        op = to_unary_expr(op).op();
        // fall through to the typecast path below
      }
      else if(
        expr.type().id() == ID_struct_tag &&
        (elaborate_class_template(expr.type()), !cpp_is_pod(expr.type())))
      {
        // N5008 [expr.type.conv]/2: `T{...}` DIRECT-LIST-INITIALIZES a
        // prvalue of type T; for a class type that is [dcl.init.list]/3
        // -- aggregate initialization for aggregates, otherwise
        // constructor selection per [over.match.list] -- NOT the
        // C compound-literal member-wise initialization below, which
        // poured `std::ofstream{name}`'s string into the stream's first
        // member ("invalid implicit conversion ... to std::streamsize").
        // The class template is elaborated BEFORE the POD judgment:
        // cpp_is_pod inspects the members for user-declared special
        // functions, and an un-elaborated instance would be
        // misclassified as POD (see convert_initializer).

        // [dcl.init.list]/3.4: aggregates initialize member-wise; the
        // helper declines for classes with user-declared constructors.
        if(!op.operands().empty())
        {
          auto aggregate_value = braced_return_aggregate_value(expr.type(), op);
          if(aggregate_value.has_value())
          {
            expr.swap(*aggregate_value);
            return;
          }
        }

        // [over.match.list]/1 phase 1: a viable initializer-list
        // constructor consumes the whole list.
        if(
          !op.operands().empty() &&
          has_viable_init_list_constructor(expr.type(), op))
        {
          auto il_val = build_init_list_argument(expr.type(), op);
          if(il_val.has_value())
          {
            already_typechecked_exprt::make_already_typechecked(*il_val);
            exprt::operandst ctor_args;
            ctor_args.push_back(std::move(*il_val));
            exprt temporary;
            new_temporary(
              expr.source_location(), expr.type(), ctor_args, temporary);
            expr.swap(temporary);
            return;
          }
        }

        // [over.match.list]/1 phase 2: the elements are arguments to a
        // constructor; an empty list value-initializes
        // ([dcl.init.list]/3.5, the default constructor).
        exprt::operandst ctor_args;
        for(auto &element : op.operands())
          ctor_args.push_back(element);
        exprt temporary;
        new_temporary(
          expr.source_location(), expr.type(), ctor_args, temporary);
        expr.swap(temporary);
        return;
      }
      else
      {
        // just do a normal initialization
        do_initializer(op, expr.type(), false);

        // This produces a struct-expression,
        // union-expression, array-expression,
        // or an expression for a pointer or scalar.
        // We produce a compound_literal expression.
        exprt tmp(ID_compound_literal, expr.type());
        tmp.add_to_operands(std::move(op));
        expr = tmp;
        expr.set(ID_C_lvalue, true); // these are l-values
        return;
      }
    }

    // Reject casts of non-static member functions — they require an
    // object and cannot be used as values.
    if(
      op.id() == ID_address_of && op.get_bool(ID_C_implicit) &&
      to_address_of_expr(op).object().type().id() == ID_code &&
      !to_code_type(to_address_of_expr(op).object().type())
         .get(ID_C_member_name)
         .empty())
    {
      error().source_location = expr.find_source_location();
      error() << "invalid use of non-static member function" << eom;
      throw 0;
    }

    // An operand of reference type (e.g. the result of
    // `static_cast<T&&>(x)`, as produced by std::forward in a function
    // template) denotes the referred object.  The cast helpers below
    // operate on the (non-reference) referred value -- const_typecast even
    // has a precondition to that effect -- and [expr.type.conv]/[conv.lval]
    // require the usual reference-binding/lvalue-to-rvalue handling.  Strip
    // the reference here so e.g. `T(static_cast<T&&>(x))` type-checks.
    if(is_reference(op.type()))
      add_implicit_dereference(op);

    // A cast the front end generates to a DIRECT base class of the operand's
    // class (the implicit copy/move constructors and assignment operators,
    // [class.copy.ctor]/14, [class.copy.assign]/12; base initializers,
    // [class.base.init]/2): it designates the direct base subobject, also
    // when the class occurs as an indirect base as well ([class.mi]/3).
    if(
      expr.get_bool(ID_C_direct_base_cast) && expr.type().id() == ID_pointer &&
      (op.type().id() == ID_pointer || op.type().id() == ID_struct_tag))
    {
      const bool to_reference =
        is_reference(expr.type()) || is_rvalue_reference(expr.type());
      exprt address = op;
      if(to_reference && op.id() == ID_dereference)
        address = to_dereference_expr(op).pointer();
      else if(to_reference)
        address = address_of_exprt{op};
      const typet &from_class = address.type().id() == ID_pointer
                                  ? to_pointer_type(address.type()).base_type()
                                  : address.type();
      const typet &to_class = to_pointer_type(expr.type()).base_type();
      if(
        address.type().id() == ID_pointer && from_class.id() == ID_struct_tag &&
        to_class.id() == ID_struct_tag &&
        to_struct_tag_type(from_class).get_identifier() !=
          to_struct_tag_type(to_class).get_identifier())
      {
        make_ptr_typecast(
          address,
          to_pointer_type(expr.type()),
          /*static_virtual_base_offset=*/false,
          /*direct_base=*/true);
        expr.swap(address);
        add_implicit_dereference(expr);
        return;
      }
    }

    exprt new_expr;

    if(
      const_typecast(op, expr.type(), new_expr) ||
      static_typecast(op, expr.type(), new_expr, false) ||
      reinterpret_typecast(op, expr.type(), new_expr, false))
    {
      expr = new_expr;
      add_implicit_dereference(expr);
    }
    else
    {
      error().source_location = expr.find_source_location();
      error() << "invalid explicit cast:\n"
              << "operand type: '" << to_string(op.type()) << "'\n"
              << "casting to: '" << to_string(expr.type()) << "'" << eom;
      throw 0;
    }
  }
  else
  {
    error().source_location = expr.find_source_location();
    error() << "explicit typecast expects 0 or 1 operands" << eom;
    throw 0;
  }
}

bool cpp_typecheckt::has_viable_init_list_constructor(
  const typet &type,
  const exprt &init_list)
{
  if(type.id() != ID_struct_tag)
    return false;

  const struct_typet &class_type = follow_tag(to_struct_tag_type(type));
  for(const auto &c : class_type.components())
  {
    if(c.type().id() != ID_code)
      continue;
    if(to_code_type(c.type()).return_type().id() != ID_constructor)
      continue;
    // N5008 [over.match.list]/1: explicit constructors ARE candidates; only
    // in copy-list-initialization is choosing one ill-formed.  The parser
    // marks the direct forms (`T x{...}', `T{...}', `new T{...}').
    if(c.get_bool(ID_is_explicit) && !init_list.get_bool(ID_C_direct_list_init))
      continue;
    const auto &params = to_code_type(c.type()).parameters();
    if(params.size() < 2)
      continue;
    typet p1 = params[1].type();
    if(is_reference(p1))
      p1 = to_reference_type(p1).base_type();
    if(p1.id() != ID_struct_tag)
      continue;
    if(
      id2string(to_struct_tag_type(p1).get_identifier())
        .find("tag-initializer_list<") == std::string::npos)
      continue;

    // The remaining parameters must be defaulted for the constructor to
    // accept a bare braced-init-list as its initializer_list argument.
    bool extras_default = true;
    for(std::size_t i = 2; i < params.size(); ++i)
    {
      if(!params[i].has_default_value())
      {
        extras_default = false;
        break;
      }
    }
    if(!extras_default)
      continue;

    // [over.match.list]/1 phase 1.1 applies only if this initializer-list
    // constructor is *viable* for the braced-init-list: each element must
    // be convertible to the initializer_list's element type.  Otherwise
    // phase 1.2 applies (e.g. `std::string{p}` for `const char *p` must
    // select `string(const char *)`, not the non-viable
    // `string(initializer_list<char>)`).
    typet elem_u = initializer_list_element_type(to_struct_tag_type(p1));
    const bool got_u = elem_u.is_not_nil();
    // If the element type cannot be determined, keep the prior behaviour
    // (treat the initializer-list constructor as applicable).
    if(!got_u)
      return true;

    bool viable = true;
    for(const auto &el : init_list.operands())
    {
      // A nested braced-init-list element list-initializes the element
      // type; leave that to the constructor to validate
      // (implicit_conversion_sequence does not model list-initialization).
      // Only a non-braced element that is not convertible to the element
      // type makes the initializer-list constructor non-viable.
      if(el.id() == ID_initializer_list)
        continue;
      exprt tc = el;
      unsigned rank = 0;
      try
      {
        typecheck_expr(tc);
      }
      catch(...)
      {
        viable = false;
        break;
      }
      if(!implicit_conversion_sequence(tc, elem_u, rank))
      {
        viable = false;
        break;
      }
    }
    if(viable)
      return true;
  }

  return false;
}

void cpp_typecheckt::typecheck_expr_explicit_constructor_call(exprt &expr)
{
  // C++17 class template argument deduction ([over.match.class.deduct]):
  // `C{...}` / `C(...)` naming a class template written without a
  // template-argument-list deduces the arguments from the initializer before
  // construction.  Without this, the prvalue form (e.g. `auto x = Box{5}`)
  // failed in typecheck_type below with "found no match for symbol 'Box'".
  if(expr.type().id() == ID_cpp_name)
  {
    const cpp_namet &ctad_name =
      to_cpp_name(static_cast<const irept &>(expr.type()));
    std::vector<exprt> ctad_args;
    if(
      expr.operands().size() == 1 &&
      expr.operands().front().id() == ID_initializer_list)
    {
      for(const auto &a : expr.operands().front().operands())
        ctad_args.push_back(a);
    }
    else
      ctad_args = expr.operands();

    if(!ctad_args.empty())
    {
      if(auto deduced = deduce_class_template_arguments(ctad_name, ctad_args))
      {
        expr.type() = *deduced;
        expr.set("#ctad_deduced", true);
      }
    }
  }

  typecheck_type(expr.type());
  // N5008 [expr.type.conv]/2 + [temp.inst]/2: `T(...)' / `T{...}' creates an
  // object of T, which must be complete (its constructors and, for an
  // aggregate, its elements decide the initialization)
  elaborate_class_template(expr.type());

  // N5008 [expr.type.conv]/2: `void()' and `void{}' are prvalues of type
  // void that perform no initialization.
  if(
    expr.type().id() == ID_empty &&
    (expr.operands().empty() ||
     (expr.operands().size() == 1 &&
      expr.operands().front().id() == ID_initializer_list &&
      expr.operands().front().operands().empty())))
  {
    exprt result =
      typecast_exprt{from_integer(0, signed_int_type()), empty_typet{}};
    result.add_source_location() = expr.source_location();
    expr.swap(result);
    return;
  }

  // N5008 [dcl.init.general]/9: "A program that calls for
  // default-initialization or value-initialization of an entity of reference
  // type is ill-formed."  `T()` with T = `int(&)[5]` (owning_view's
  // `_Range _M_r = _Range()` default member initializer once _Range is
  // deduced as a reference) used to reach cpp_constructor and abort on its
  // not-a-reference invariant; in a requires-expression / SFINAE context the
  // error is what makes the requirement unsatisfied.
  if(expr.operands().empty() && is_reference(expr.type()))
  {
    error().source_location = expr.find_source_location();
    error() << "value-initialization of reference type '"
            << to_string(expr.type()) << "'" << eom;
    throw 0;
  }

  // N5008 [dcl.init.general]/16.6.2.2 (C++20 parenthesized aggregate
  // initialization): `T(a1, ..., an)` with T an aggregate and no viable
  // constructor initializes the aggregate's elements from the
  // expression-list, exactly as the braced form.  An aggregate has no
  // user-declared constructors ([dcl.init.aggr]/1) -- its members may
  // (pair<reverse_iterator, ...>), which merely makes it non-POD -- so
  // re-shape the multi-operand call into the single initializer-list
  // operand that both the POD typecast path and the non-POD aggregate
  // branch below expect (`pair(a, b)` from CTAD used to die with
  // "explicit typecast expects 0 or 1 operands").
  // A SINGLE argument takes the same route when it cannot be a
  // copy/move ([dcl.init.general]/16.6.1 considers constructors first;
  // for an aggregate only the synthesized copy/move are candidates, so
  // an argument of a DIFFERENT, non-derived type falls through to
  // /16.6.2.2 aggregate initialization: `take_view<int>(3)` from the
  // libc++ views::take CTAD initializes the single member from 3;
  // previously it fell into the explicit-cast path and died with
  // "invalid explicit cast").
  const bool ctad_deduced = expr.get_bool("#ctad_deduced");
  expr.remove("#ctad_deduced");
  if(expr.operands().size() >= 1 && expr.type().id() == ID_struct_tag)
  {
    const struct_typet &agg_type = follow_tag(to_struct_tag_type(expr.type()));
    // [dcl.init.aggr]/1: a user-declared constructor TEMPLATE or an
    // inherited constructor also disqualifies the aggregate; neither is a
    // component, the type carries flags (`ref_view{arr}` used to be
    // aggregate-initialized from the array, skipping ref_view's
    // forwarding constructor template).
    bool has_user_ctor = agg_type.get_bool("has_template_constructor") ||
                         agg_type.get_bool("has_inherited_constructor");
    for(const auto &c : agg_type.components())
    {
      if(has_user_ctor)
        break;
      if(
        c.type().id() == ID_code &&
        to_code_type(c.type()).return_type().id() == ID_constructor &&
        !c.get_bool(ID_from_base) && !c.type().get_bool("#is_implicit_ctor"))
      {
        has_user_ctor = true;
        break;
      }
    }
    bool single_is_copyish = false;
    if(expr.operands().size() == 1)
    {
      // look through an already-typechecked wrapper: the call re-route
      // wraps arguments it has type-checked, and the base-element
      // detection below needs the VALUE's type
      const exprt &op0 = expr.operands().front().id() == ID_already_typechecked
                           ? to_unary_expr(expr.operands().front()).op()
                           : expr.operands().front();
      if(op0.id() == ID_initializer_list)
        single_is_copyish = true; // already list-shaped: leave as-is
      else
      {
        typet op_t = op0.type();
        if(is_reference(op_t))
          op_t = to_reference_type(op_t).base_type();
        if(
          op_t.id() == ID_struct_tag &&
          (to_struct_tag_type(op_t).get_identifier() ==
             to_struct_tag_type(expr.type()).get_identifier() ||
           subtype_typecast(
             follow_tag(to_struct_tag_type(op_t)),
             follow_tag(to_struct_tag_type(expr.type())))))
          single_is_copyish = true;
        // N5008 [dcl.init.aggr]/2.2: the aggregate's elements START with
        // its direct base classes.  A single operand whose type is a
        // BASE of the deduced aggregate initializes that base element
        // (the libc++ `__range_adaptor_closure_t(__bind_back(...))`
        // CTAD shape); route it through cpp_constructor, whose
        // aggregate-with-bases branch performs the base-wise
        // initialization -- the flattened-initializer reshape below
        // cannot represent a base element.
        else if(
          ctad_deduced && op_t.id() == ID_struct_tag &&
          subtype_typecast(
            follow_tag(to_struct_tag_type(expr.type())),
            follow_tag(to_struct_tag_type(op_t))))
        {
          exprt::operandst ctor_args = expr.operands();
          exprt temporary;
          new_temporary(
            expr.source_location(), expr.type(), ctor_args, temporary);
          expr.swap(temporary);
          return;
        }
        // an operand of scalar/other type may still CONVERT to the
        // class via a conversion function; keep those on the cast path
        // unless this is aggregate initialization with no more
        // arguments than elements ([dcl.init.aggr]/5 value-initializes
        // the rest).
        std::size_t n_data_members = 0;
        for(const auto &c : agg_type.components())
        {
          if(
            c.type().id() != ID_code && !c.get_bool(ID_is_type) &&
            !c.get_bool(ID_is_static) && !c.get_is_padding())
            ++n_data_members;
        }
        if(n_data_members < 1)
          single_is_copyish = true;
        // ... and only within the class-template-argument-deduction
        // flow ([over.match.class.deduct] via the hook above): an
        // explicitly-written single-argument functional cast keeps the
        // conversion path (existing behavior; a reshape there produced
        // mismatched member lists downstream).
        if(!ctad_deduced)
          single_is_copyish = true;
      }
    }
    if(!has_user_ctor && !single_is_copyish)
    {
      exprt init_list(ID_initializer_list, expr.type());
      init_list.operands().swap(expr.operands());
      init_list.add_source_location() = expr.source_location();
      expr.operands().clear();
      expr.add_to_operands(std::move(init_list));
    }
  }

  if(cpp_is_pod(expr.type()))
  {
    // N5008 [dcl.init.list]/3.2: list-initialization from a braced list
    // whose single element is of the SAME class type (or derived) is
    // copy-initialization from that element, not element-wise
    // aggregate initialization -- `Base{b}` with b a Base copies b.
    if(
      expr.operands().size() == 1 &&
      expr.operands().front().id() == ID_initializer_list &&
      expr.operands().front().operands().size() == 1 &&
      expr.type().id() == ID_struct_tag)
    {
      exprt &elem = to_unary_expr(expr.operands().front()).op();
      exprt elem_tc = elem;
      typecheck_expr(elem_tc);
      typet elem_type = elem_tc.type();
      if(is_reference(elem_type))
        elem_type = to_reference_type(elem_type).base_type();
      if(
        elem_type.id() == ID_struct_tag &&
        (to_struct_tag_type(elem_type).get_identifier() ==
           to_struct_tag_type(expr.type()).get_identifier() ||
         subtype_typecast(
           follow_tag(to_struct_tag_type(elem_type)),
           follow_tag(to_struct_tag_type(expr.type())))))
      {
        already_typechecked_exprt::make_already_typechecked(elem_tc);
        exprt unwrapped = std::move(elem_tc);
        expr.operands().clear();
        expr.add_to_operands(std::move(unwrapped));
      }
    }
    expr.id("explicit-typecast");
    typecheck_expr_main(expr);
  }
  else
  {
    // Aggregate initialization from braced-init-list for non-POD
    // aggregates (e.g., structs with reference members).
    if(
      expr.operands().size() == 1 &&
      expr.operands().front().id() == ID_initializer_list &&
      !expr.operands().front().operands().empty() &&
      expr.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(expr.type()));

      // Check whether the struct has any non-copy constructor.  A
      // constructor TEMPLATE or an inherited constructor is not a component;
      // the type carries flags for them ([dcl.init.aggr]/1 counts both).
      bool has_non_copy_ctor =
        struct_type.get_bool("has_template_constructor") ||
        struct_type.get_bool("has_inherited_constructor");
      for(const auto &c : struct_type.components())
      {
        if(has_non_copy_ctor)
          break;
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &code_type = to_code_type(c.type());
        if(code_type.return_type().id() != ID_constructor)
          continue;
        // N5008 [dcl.init.aggr]/1: only USER-declared (or inherited)
        // constructors disqualify an aggregate.  A user-declared
        // destructor makes the front end synthesize default/copy/move
        // constructors; treating those as disqualifying sent the braced
        // temporary `itert{&g}` of a destructor-bearing aggregate into
        // constructor overload resolution, which found no match.
        if(c.type().get_bool("#is_implicit_ctor"))
          continue;
        const auto &params = code_type.parameters();
        // A copy/move constructor takes a single (reference) parameter of the
        // class's OWN type.  A converting constructor such as `It(const S&)`
        // with S a DIFFERENT type also has two parameters whose second is a
        // reference, but it is NOT a copy/move constructor -- and being
        // user-declared it makes the class a non-aggregate ([dcl.init.aggr]/1),
        // so `It{arg}` must call that constructor rather than perform aggregate
        // initialization.  Only skip genuine copy/move constructors here.
        if(params.size() == 2 && is_reference(params[1].type()))
        {
          typet param_base = to_reference_type(params[1].type()).base_type();
          param_base.remove(ID_C_constant);
          param_base.remove(ID_C_volatile);
          const bool is_self =
            param_base.id() == ID_struct_tag &&
            expr.type().id() == ID_struct_tag &&
            to_struct_tag_type(param_base).get_identifier() ==
              to_struct_tag_type(expr.type()).get_identifier();
          if(is_self)
            continue;
        }
        has_non_copy_ctor = true;
        break;
      }

      // N5008 [dcl.init.aggr]/4.2 with [class.temporary]/2: as for a
      // declared aggregate (aggregate_member_initialization), elements of a
      // non-POD class type are constructed in the temporary rather than
      // copied bitwise from temporaries that are then destroyed
      // (`return A{owner(6), 2};').
      if(
        !has_non_copy_ctor && struct_type.bases().empty() &&
        has_non_pod_class_member(struct_type))
      {
        const exprt::operandst ops_copy = expr.operands().front().operands();
        const struct_typet struct_copy = struct_type;
        exprt new_object{ID_new_object, expr.type()};
        new_object.set(ID_C_lvalue, true);
        new_object.add_source_location() = expr.source_location();
        code_blockt block;
        aggregate_member_initialization(
          new_object, struct_copy, ops_copy, expr.source_location(), block);
        side_effect_exprt temporary{
          ID_temporary_object, expr.type(), expr.source_location()};
        temporary.set(ID_mode, ID_cpp);
        temporary.set(ID_C_lvalue, true);
        temporary.add(ID_initializer) = std::move(block);
        expr = std::move(temporary);
        return;
      }

      if(!has_non_copy_ctor)
      {
        const auto &ops = expr.operands().front().operands();
        // all-zero start: the layout's padding components are present
        auto result_opt =
          zero_struct_value(expr.type(), expr.source_location());
        struct_exprt result =
          result_opt.has_value() ? *result_opt : struct_exprt({}, expr.type());
        std::size_t idx = 0;
        bool aggregate = result_opt.has_value();
        // N5008 [dcl.init.aggr]/2.2: the aggregate's elements START
        // with the direct base classes, in declaration order.  When a
        // direct base is EMPTY (no data members -- the libc++
        // range-adaptor `__take_closure{{}, __n}` shape, whose base
        // __range_adaptor_closure<...> is empty), its element
        // initializes nothing; consume one leading empty braced
        // clause per base so the remaining clauses pair with the data
        // members.  (Bases WITH data members contribute from_base
        // components, which this reshape does not model; those keep
        // the constructor path.)
        for(const auto &b : struct_type.find(ID_bases).get_sub())
        {
          if(b.is_nil())
            continue;
          if(
            idx < ops.size() && ops[idx].id() == ID_initializer_list &&
            ops[idx].operands().empty())
          {
            ++idx;
          }
        }
        for(const auto &c : struct_type.components())
        {
          if(!aggregate)
            break;
          if(
            c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
            c.get_bool(ID_is_static) || c.type().id() == ID_code ||
            c.get_is_padding())
          {
            continue;
          }
          if(idx < ops.size())
          {
            exprt val = ops[idx++];
            typecheck_expr(val);
            if(is_reference(c.type()))
              reference_initializer(val, to_reference_type(c.type()));
            else
              implicit_typecast(val, c.type());
            set_struct_member_value(result, struct_type, c, std::move(val));
          }
          else
          {
            aggregate = false;
            break;
          }
        }
        if(aggregate)
        {
          result.add_source_location() = expr.source_location();
          expr = std::move(result);
          return;
        }
      }
    }

    exprt e = expr;

    // An empty braced-init-list {} means value-initialization,
    // which for class types calls the default constructor.
    if(
      e.operands().size() == 1 &&
      e.operands().front().id() == ID_initializer_list &&
      e.operands().front().operands().empty())
    {
      e.operands().clear();
    }

    // Direct-list-initialization: TYPE{a, b, c} should try to match
    // constructors with the individual elements of the braced-init-list.
    //
    // [over.match.list]/2 distinguishes two phases:
    //   2.1: try initializer-list ctors first, with the brace-init-list
    //        as a single argument.
    //   2.2: if 2.1 finds no viable ctor, retry with all ctors and the
    //        elements of the brace-init-list as the argument list.
    //
    // The previous unconditional expansion of `{e1, ..., en}` into
    // operands `[e1, ..., en]` skipped phase 2.1, so e.g.
    //   std::vector<X>{x1, x2}
    // never matched the `vector(initializer_list<X>, alloc&)` ctor and
    // failed when no `vector(X, X, ...)` ctor existed.  When the
    // target class has a non-explicit `initializer_list<U>` ctor (the
    // canonical phase-2.1 candidate), keep the brace-init-list as a
    // single argument so overload resolution can find it.  Otherwise
    // fall through to the existing phase-2.2 expansion.
    if(
      e.operands().size() == 1 &&
      e.operands().front().id() == ID_initializer_list &&
      !e.operands().front().operands().empty())
    {
      if(!has_viable_init_list_constructor(e.type(), e.operands().front()))
      {
        exprt::operandst expanded = std::move(e.operands().front().operands());
        e.operands() = std::move(expanded);
      }
    }

    // The braced-init operands have already been type-checked above.  Mark
    // them so that cpp_constructor (reached via new_temporary) does not
    // re-type-check them: re-type-checking a reference-member access that has
    // already had its implicit dereference applied (e.g. `*this->root`) would
    // re-apply that dereference, producing an ill-formed `*(*this->root)`
    // ("operand of unary * is not a pointer").
    for(auto &op : e.operands())
      already_typechecked_exprt::make_already_typechecked(op);

    // C++20 parenthesized aggregate initialization (P0960; N5008
    // [expr.type.conv]/2 via [dcl.init.general]/16.6.2.2): constructors
    // are considered FIRST, but when overload resolution finds no
    // viable constructor and T is an aggregate, `T(a1, ..., an)`
    // initializes the aggregate's elements from the expression-list.
    // libstdc++'s C++20 forward_as_tuple constructs
    // `tuple<_Elements...>(__args...)` where tuple has no matching
    // constructor of its own -- without the fallback the enclosing
    // body was dropped and std::map's piecewise-constructed key was
    // lost.
    if(
      config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP20 &&
      e.type().id() == ID_struct_tag && !e.operands().empty() &&
      e.operands().front().id() != ID_initializer_list)
    {
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(e.type()));
      bool user_ctor = struct_type.get_bool("has_template_constructor") ||
                       struct_type.get_bool("has_inherited_constructor");
      for(const auto &c : struct_type.components())
      {
        if(
          user_ctor || c.type().id() != ID_code || c.get_bool(ID_from_base) ||
          to_code_type(c.type()).return_type().id() != ID_constructor)
          continue;
        if(!c.type().get_bool("#is_implicit_ctor"))
          user_ctor = true;
      }
      if(!user_ctor)
      {
        const std::size_t errors_before_ctor_attempt =
          get_message_handler().get_message_count(messaget::M_ERROR);
        try
        {
          exprt tmp = expr;
          new_temporary(e.source_location(), e.type(), e.operands(), tmp);
          expr.swap(tmp);
          return;
        }
        catch(...)
        {
          // no viable constructor: aggregate-initialize below; the
          // attempt's diagnostics are not errors ([dcl.init.general]
          // /16.6.2.2 falls back rather than failing)
          get_message_handler().set_message_count(
            messaget::M_ERROR, errors_before_ctor_attempt);
        }
        exprt::operandst ops = e.operands();
        // all-zero start: the layout's padding components are present, and
        // [dcl.init.aggr]/5's remaining elements (default member
        // initializers or value-initialization) are approximated by zero.
        auto result_opt = zero_struct_value(e.type(), e.source_location());
        struct_exprt result =
          result_opt.has_value() ? *result_opt : struct_exprt({}, e.type());
        std::size_t idx = 0;
        bool aggregate_ok = result_opt.has_value();
        for(const auto &c : struct_type.components())
        {
          if(!aggregate_ok)
            break;
          if(
            c.get_bool(ID_is_type) || c.get_bool(ID_is_static) ||
            c.type().id() == ID_code || c.get_is_padding())
            continue;
          if(idx < ops.size())
          {
            exprt val = ops[idx++];
            if(val.id() == ID_already_typechecked)
              val = to_already_typechecked_expr(val).get_expr();
            if(is_reference(c.type()))
              reference_initializer(val, to_reference_type(c.type()));
            else
              implicit_typecast(val, c.type());
            set_struct_member_value(result, struct_type, c, std::move(val));
          }
        }
        if(aggregate_ok && idx == ops.size())
        {
          result.add_source_location() = expr.source_location();
          expr = std::move(result);
          return;
        }
        // fall through to the plain constructor path to reproduce the
        // original diagnostic
      }
    }

    new_temporary(e.source_location(), e.type(), e.operands(), expr);
  }
}

/// Type-check a `typeid` expression ([expr.typeid]).
///
/// The result is an lvalue of type `const std::type_info` that refers to a
/// unique-per-type object ([type.info]): two `type_info` objects compare
/// equal if and only if they denote the same type.  We model this by mapping
/// each type (after stripping references and top-level cv-qualifiers, per
/// [expr.typeid]) to a single static `std::type_info` object whose `__name`
/// member points at a distinct string, so that libstdc++'s
/// `type_info::operator==` (which compares `__name`) yields type identity.
///
/// For the `typeid(expression)` form, the static type of the operand is used;
/// a non-polymorphic operand is unevaluated.  The dynamic type of a
/// polymorphic glvalue is not modelled and is approximated by its static
/// type.
void cpp_typecheckt::typecheck_expr_typeid(exprt &expr)
{
  // [expr.typeid]/4: the program is ill-formed unless <typeinfo> has been
  // included before the use of typeid.
  const struct_tag_typet ti_type{"std::tag-type_info"};
  if(!symbol_table.has_symbol(ti_type.get_identifier()))
  {
    error().source_location = expr.find_source_location();
    error() << "typeid requires <typeinfo> to be included" << eom;
    throw 0;
  }

  const source_locationt source_location = expr.find_source_location();

  // Determine the type T whose std::type_info is requested.
  typet t;
  if(expr.has_operands())
  {
    // typeid(expression): use the static type of the operand.  Per
    // [expr.typeid]/3 a non-polymorphic operand is an unevaluated operand,
    // so we only retain its type and discard the operand itself.
    exprt &op = to_unary_expr(expr).op();
    typecheck_expr(op);
    t = op.type();
  }
  else
  {
    // typeid(type-id) -- but the operand may have been mis-parsed as a
    // type when it is in fact an expression (e.g. typeid(x) where x is a
    // variable).  Resolve a cpp_name to decide, as for sizeof.
    typet type_arg = static_cast<const typet &>(expr.find(ID_type_arg));
    if(type_arg.id() == ID_cpp_name)
    {
      cpp_typecheck_fargst fargs;
      exprt resolved = resolve(
        to_cpp_name(static_cast<const irept &>(type_arg)),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);
      // Whether `resolved` is a type or an (unevaluated) expression, its
      // type is the static type whose std::type_info is requested.
      t = resolved.type();
    }
    else
    {
      typecheck_type(type_arg);
      t = type_arg;
    }
  }

  // [expr.typeid]/5: typeid ignores top-level cv-qualifiers, and references
  // are stripped to the referred-to type.  Types that differ only in these
  // share the same type_info object.
  if(is_reference(t))
    t = to_reference_type(t).base_type();
  t.remove(ID_C_constant);
  t.remove(ID_C_volatile);

  // Canonical key so that equal types share a single type_info object
  // ([expr.typeid]/1: the type_info denotes the type).  Use the C++
  // front-end's own type naming -- for a class type that is its tag
  // identifier, unique per class ([basic.scope.scope], [class.pre]) --
  // rather than the C linker's structural type2name, which spells out
  // every component of a class: a class template instance's components
  // include its member templates, whose declared parameter types are
  // still template parameters (`unassigned`) and made type2name throw,
  // so `typeid(_Functor)` in libstdc++'s _Function_handler::_M_manager
  // aborted for any functor with a member template (std::_Bind ->
  // std::function).
  const std::string key = cpp_type2name(t);
  const irep_idt sym_id = "typeid$" + key;

  if(!symbol_table.has_symbol(sym_id))
  {
    const struct_typet &ti_struct = follow_tag(ti_type);

    // Build a value for the type_info object: the `__name` member points at
    // a string that is distinct for distinct types (so libstdc++'s
    // type_info::operator== yields type identity); all other members
    // (notably the vtable pointer, which is never used since the modelled
    // operations involve no virtual dispatch on type_info) are zero.
    string_constantt name_str{key};
    index_exprt first_char{name_str, from_integer(0, c_index_type())};

    struct_exprt::operandst field_values;
    for(const auto &comp : ti_struct.components())
    {
      // Skip non-data components (member functions, static members and
      // member types): they are not part of the object's data layout.
      if(
        comp.type().id() == ID_code || comp.get_bool(ID_is_static) ||
        comp.get_bool(ID_is_type))
      {
        continue;
      }

      if(comp.get_base_name() == "__name" && comp.type().id() == ID_pointer)
      {
        address_of_exprt name_addr{first_char};
        name_addr.type() = to_pointer_type(comp.type());
        field_values.push_back(std::move(name_addr));
      }
      else
      {
        auto zero =
          itanium_abi_cpp_zero_initializer(comp.type(), source_location, *this);
        CHECK_RETURN(zero.has_value());
        field_values.push_back(std::move(*zero));
      }
    }

    struct_exprt ti_value{std::move(field_values), ti_type};
    ti_value.add_source_location() = source_location;

    symbolt ti_symbol;
    ti_symbol.name = sym_id;
    ti_symbol.base_name = sym_id;
    ti_symbol.type = ti_type;
    ti_symbol.type.set(ID_C_constant, true);
    ti_symbol.mode = ID_cpp;
    ti_symbol.is_static_lifetime = true;
    ti_symbol.is_lvalue = true;
    ti_symbol.location = source_location;
    ti_symbol.value = std::move(ti_value);
    symbol_table.insert(std::move(ti_symbol));
  }

  // The result is a const lvalue referring to the type_info object.
  typet const_ti_type = ti_type;
  const_ti_type.set(ID_C_constant, true);
  symbol_exprt result{sym_id, const_ti_type};
  result.set(ID_C_lvalue, true);
  result.add_source_location() = source_location;
  expr = std::move(result);
}

void cpp_typecheckt::typecheck_expr_this(exprt &expr)
{
  if(cpp_scopes.current_scope().class_identifier.empty())
  {
    error().source_location = expr.find_source_location();
    error() << quote_begin << "this" << quote_end << " is not allowed here"
            << eom;
    throw 0;
  }

  const exprt &this_expr = cpp_scopes.current_scope().this_expr;
  const source_locationt source_location = expr.find_source_location();

  if(this_expr.is_nil())
  {
    error().source_location = source_location;
    error() << "'this' used outside class context" << eom;
    throw 0;
  }
  PRECONDITION(this_expr.type().id() == ID_pointer);

  expr = this_expr;
  expr.add_source_location() = source_location;
}

void cpp_typecheckt::typecheck_expr_delete(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "delete expects one operand" << eom;
    throw 0;
  }

  const irep_idt statement = expr.get(ID_statement);

  if(statement == ID_cpp_delete)
  {
  }
  else if(statement == ID_cpp_delete_array)
  {
  }
  else
    UNREACHABLE;

  typet pointer_type = to_unary_expr(expr).op().type();

  if(pointer_type.id() != ID_pointer)
  {
    error().source_location = expr.find_source_location();
    error() << "delete takes a pointer type operand, but got '"
            << to_string(pointer_type) << "'" << eom;
    throw 0;
  }

  // remove any const-ness of the argument
  // (which would impair the call to the destructor)
  to_pointer_type(pointer_type).base_type().remove(ID_C_constant);

  // delete expressions are always void
  expr.type() = typet(ID_empty);

  // we provide the right destructor, for the convenience
  // of later stages
  exprt new_object(ID_new_object, to_pointer_type(pointer_type).base_type());
  new_object.add_source_location() = expr.source_location();
  new_object.set(ID_C_lvalue, true);

  auto destructor_code =
    cpp_destructor(expr.source_location(), new_object, false);

  already_typechecked_exprt::make_already_typechecked(new_object);

  if(destructor_code.has_value())
  {
    // this isn't typechecked yet
    typecheck_code(destructor_code.value());
    expr.set(ID_destructor, destructor_code.value());
  }
  else
    expr.set(ID_destructor, nil_exprt());
}

void cpp_typecheckt::typecheck_expr_typecast(exprt &)
{
// should not be called
#if 0
  std::cout << "E: " << expr.pretty() << '\n';
  UNREACHABLE;
#endif
}

/// The class denoted by the nested-name-specifier of the qualified name
/// \p name (`N' in `N::m'), if it names a class.
std::optional<irep_idt> cpp_typecheckt::naming_class_of(const cpp_namet &name)
{
  cpp_namet qualifier;
  const auto &subs = name.get_sub();
  std::size_t last = subs.size();
  while(last > 0 && subs[last - 1].id() != ID_scope_resolution)
    --last;
  if(last <= 1)
    return {}; // `::m' or unqualified
  for(std::size_t i = 0; i + 1 < last; ++i)
    qualifier.get_sub().push_back(subs[i]);
  qualifier.set(ID_C_source_location, name.source_location());
  try
  {
    sfinae_contextt sfinae_guard{*this};
    const exprt resolved = resolve(
      qualifier, cpp_typecheck_resolvet::wantt::TYPE, cpp_typecheck_fargst{});
    if(resolved.id() == ID_type && resolved.type().id() == ID_struct_tag)
    {
      return to_struct_tag_type(resolved.type()).get_identifier();
    }
  }
  catch(...)
  {
  }
  return {};
}

void cpp_typecheckt::typecheck_expr_member(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "member operator expects one operand" << eom;
    throw 0;
  }

  exprt &op0 = to_unary_expr(expr).op();
  add_implicit_dereference(op0);

  // The notation for explicit calls to destructors can be used regardless
  // of whether the type defines a destructor.  This allows you to make such
  // explicit calls without knowing if a destructor is defined for the type.
  // An explicit call to a destructor where none is defined has no effect.

  if(
    expr.find(ID_component_cpp_name).is_not_nil() &&
    to_cpp_name(expr.find(ID_component_cpp_name)).is_destructor() &&
    op0.type().id() != ID_struct && op0.type().id() != ID_struct_tag)
  {
    exprt tmp(ID_cpp_dummy_destructor);
    tmp.add_source_location() = expr.source_location();
    expr.swap(tmp);
    return;
  }

  // The member operator will trigger template elaboration
  elaborate_class_template(op0.type());

  if(op0.type().id() != ID_struct_tag && op0.type().id() != ID_union_tag)
  {
    error().source_location = expr.find_source_location();
    error() << "member operator requires struct/union type "
            << "on left hand side but got '" << to_string(op0.type()) << "'"
            << eom;
    throw 0;
  }

  const struct_union_typet &type =
    op0.type().id() == ID_struct_tag
      ? static_cast<const struct_union_typet &>(
          follow_tag(to_struct_tag_type(op0.type())))
      : static_cast<const struct_union_typet &>(
          follow_tag(to_union_tag_type(op0.type())));

  if(type.is_incomplete())
  {
    error().source_location = expr.find_source_location();
    error() << "member operator got incomplete type "
            << "on left hand side" << eom;
    throw 0;
  }

  irep_idt struct_identifier = type.get(ID_name);

  // N5008 [expr.prim.id.dtor] + [class.dtor]/1,6: the explicit destructor
  // call notation is valid for EVERY class, and invoking a TRIVIAL
  // destructor has no effect.  A class whose destructor is implicitly
  // declared and trivial has no synthesized destructor symbol (the POD
  // gate in typecheck_compound_body skips it), so resolving `~X` failed
  // and the failure escaped e.g. the destructibility SFINAE probe
  // `decltype(declval<T&>().~T())` -- dropping libstdc++ trait base
  // specifiers during nested instantiation (the std::optional shape).
  // Model the call with the same no-op dummy used for scalar
  // pseudo-destructor calls above.
  if(
    expr.find(ID_component_cpp_name).is_not_nil() &&
    to_cpp_name(expr.find(ID_component_cpp_name)).is_destructor())
  {
    bool has_dtor_member = false;
    for(const auto &c : type.components())
    {
      if(
        c.type().id() == ID_code &&
        to_code_type(c.type()).return_type().id() == ID_destructor)
      {
        has_dtor_member = true;
        break;
      }
    }
    if(!has_dtor_member)
    {
      exprt tmp(ID_cpp_dummy_destructor);
      tmp.add_source_location() = expr.source_location();
      expr.swap(tmp);
      return;
    }
  }

  if(expr.find(ID_component_cpp_name).is_not_nil())
  {
    cpp_namet component_cpp_name =
      to_cpp_name(expr.find(ID_component_cpp_name));

    // Per N5008 [class.access]/4 + the lazy class-body elaboration
    // discipline: if the struct has no `ID_name` set, it is a
    // residual placeholder from a failed instantiation that wasn't
    // cleanly excluded upstream.  Without this guard,
    // `cpp_scopes.set_scope("")` aborts in the lookup with
    // "id '' not found" and crashes goto-cc.  Emit a localized
    // error and throw the conventional throw-0 signal instead so
    // the failure stays a user-visible compile error in the
    // calling translation unit rather than a CBMC abort.
    if(struct_identifier.empty())
    {
      error().source_location = expr.find_source_location();
      error() << "member operator on unnamed/incomplete struct "
              << "(typically from a failed template instantiation)" << eom;
      throw 0;
    }

    // N5008 [class.access.base]/5-6: in `E1.N::m' the naming class is N, and
    // E1 must be implicitly convertible to (a pointer to) N; the member is
    // that of E1's N subobject.  It matters when a base class occurs more
    // than once in the lattice ([class.mi]/5: `d.B::i' and `d.C::i' are the
    // i of different A subobjects).  Convert E1 first, so that lookup and
    // the implicit object argument of a member function refer to it.
    if(
      component_cpp_name.is_qualified() && op0.type().id() == ID_struct_tag &&
      type.id() == ID_struct)
    {
      const auto naming_class = naming_class_of(component_cpp_name);
      if(
        naming_class.has_value() && *naming_class != struct_identifier &&
        subtype_typecast(
          to_struct_type(type), follow_tag(struct_tag_typet{*naming_class})))
      {
        exprt address = op0.id() == ID_dereference
                          ? to_dereference_expr(op0).pointer()
                          : exprt{address_of_exprt{op0}};
        pointer_typet naming_pointer =
          pointer_type(struct_tag_typet{*naming_class});
        if(op0.type().get_bool(ID_C_constant))
          naming_pointer.base_type().set(ID_C_constant, true);
        make_ptr_typecast(address, naming_pointer);
        dereference_exprt subobject{address, naming_pointer.base_type()};
        subobject.set(ID_C_lvalue, op0.get_bool(ID_C_lvalue));
        subobject.add_source_location() = op0.source_location();
        op0 = std::move(subobject);
        // The member is now looked up in N itself: drop the
        // nested-name-specifier, which need not be visible from N's scope
        // (`x.eh::m' with `eh' a member typedef of x's class).  The call
        // stays non-virtual: typecheck_side_effect_function_call decided
        // that from the qualified name before getting here.
        cpp_namet terminal;
        const auto &subs = component_cpp_name.get_sub();
        std::size_t first = subs.size();
        while(first > 0 && subs[first - 1].id() != ID_scope_resolution)
          --first;
        for(std::size_t i = first; i < subs.size(); ++i)
          terminal.get_sub().push_back(subs[i]);
        terminal.set(
          ID_C_source_location, component_cpp_name.source_location());
        expr.set(ID_component_cpp_name, terminal);
        typecheck_expr_member(expr, fargs);
        return;
      }
    }

    // go to the scope of the struct/union
    cpp_save_scopet save_scope(cpp_scopes);
    // Capture the genuine point of use ([class.access]) before navigating
    // into the object's class scope, so that member accessibility is
    // judged from the enclosing class/function rather than from the
    // object's type.
    cpp_scopet &naming_scope = cpp_scopes.current_scope();
    cpp_scopes.set_scope(struct_identifier);

    // resolve the member name in this scope
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.add_object(op0);
    new_fargs.naming_scope = &naming_scope;
    new_fargs.member_access = true;

    // N5008 [basic.lookup.qual]/6: for a ~type-name after . or ->, the
    // type-name is looked up both in the context of the entire
    // postfix-expression and in the scope of the object's class.  The
    // resolver only sees the object's class scope (we just entered it);
    // record the postfix-expression context so the destructor-typedef
    // substitution in resolve_scope can search it as well.  RAII-restored.
    struct member_access_scope_guardt
    {
      cpp_typecheckt &tc;
      cpp_scopet *saved;
      member_access_scope_guardt(cpp_typecheckt &t, cpp_scopet &use_scope)
        : tc(t), saved(t.access_judgment_scope)
      {
        tc.access_judgment_scope = &use_scope;
      }
      ~member_access_scope_guardt()
      {
        tc.access_judgment_scope = saved;
      }
    } member_access_scope_guard{*this, naming_scope};

    exprt symbol_expr = resolve(
      component_cpp_name, cpp_typecheck_resolvet::wantt::VAR, new_fargs);

    if(symbol_expr.id() == ID_dereference)
    {
      CHECK_RETURN(symbol_expr.get_bool(ID_C_implicit));
      exprt tmp = to_dereference_expr(symbol_expr).pointer();
      symbol_expr.swap(tmp);
    }

    // Soften to graceful error: typecheck_expr_member may receive
    // an unusual symbol_expr shape when resolve has fallen back to
    // a partial synthesis for an unresolvable member (for example
    // the destructor of a class whose components list has the
    // destructor but whose scope does not).  Rather than aborting
    // via DATA_INVARIANT, emit a diagnostic and throw.
    if(!(symbol_expr.id() == ID_symbol || symbol_expr.id() == ID_member ||
         symbol_expr.is_constant()))
    {
      error().source_location = expr.find_source_location();
      error() << "unresolved member expression (id=" << symbol_expr.id() << ")"
              << eom;
      throw 0;
    }

    // If it is a symbol or a constant, just return it!
    // Note: the resolver returns a symbol if the member
    // is static or if it is a constructor.

    if(symbol_expr.id() == ID_symbol)
    {
      if(
        symbol_expr.type().id() == ID_code &&
        to_code_type(symbol_expr.type()).return_type().id() == ID_constructor)
      {
        error().source_location = expr.find_source_location();
        error() << "member '"
                << lookup(symbol_expr.get(ID_identifier)).base_name
                << "' is a constructor" << eom;
        throw 0;
      }
      else
      {
        // Check if this is an instantiated member function template
        // (non-static, with a 'this' parameter).  In that case, we
        // must not treat it as a static member — fall through to the
        // member-expression path so that 'this' is added.
        // N5008 [dcl.fct]/6: an instantiated member function template with
        // an EXPLICIT object parameter (`this Self &&self') is a non-static
        // member too; the caller (typecheck_method_application) passes the
        // object as its first argument.
        if(
          symbol_expr.type().id() == ID_code &&
          !to_code_type(symbol_expr.type()).parameters().empty() &&
          (to_code_type(symbol_expr.type()).parameters().front().get_this() ||
           symbol_expr.type().get_bool("explicit_this")))
        {
          // Build a member expression so the caller adds 'this'.
          irep_idt component_name =
            to_symbol_expr(symbol_expr).get_identifier();
          expr.remove(ID_component_cpp_name);
          expr.set(ID_component_name, component_name);
          expr.type() = symbol_expr.type();
          return;
        }

        // it must be a static component
        const struct_typet::componentt &pcomp =
          type.get_component(to_symbol_expr(symbol_expr).identifier());

        // N5008 [expr.ref]/6.3, [class.member.lookup]: `this->f<T>(...)'
        // naming a static member function TEMPLATE specialization of the
        // class or of one of its bases (libc++ variant's
        // `this->__construct_alt(__get_alt<_Ip>(*this), ...)' from
        // `__assignment', three bases below `__ctor').  The specialization
        // is a symbol of its class (#member_name) but not a component of
        // the derived class the object has, so the component look-up
        // cannot vouch for it; the class relationship does.
        bool static_member_of_base = false;
        if(pcomp.is_nil() && type.id() == ID_struct)
        {
          const irep_idt &owner = symbol_expr.type().get(ID_C_member_name);
          const symbolt *owner_symbol =
            owner.empty() ? nullptr : symbol_table.lookup(owner);
          if(
            owner_symbol != nullptr && owner_symbol->type.id() == ID_struct &&
            symbol_expr.type().get_bool(ID_C_is_static))
          {
            static_member_of_base =
              owner == to_struct_tag_type(op0.type()).get_identifier() ||
              subtype_typecast(
                to_struct_type(type), to_struct_type(owner_symbol->type));
          }
        }

        if(pcomp.is_nil() && !static_member_of_base)
        {
          error().source_location = expr.find_source_location();

          error() << "'" << symbol_expr.get(ID_identifier)
                  << "' is not static member "
                  << "of class '" << to_string(op0.type()) << "'" << eom;
          throw 0;
        }
      }

      expr = symbol_expr;
      return;
    }
    else if(symbol_expr.is_constant())
    {
      expr = symbol_expr;
      return;
    }

    const irep_idt component_name = symbol_expr.get(ID_component_name);

    expr.remove(ID_component_cpp_name);
    expr.set(ID_component_name, component_name);
  }

  const irep_idt &component_name = expr.get(ID_component_name);
  INVARIANT(!component_name.empty(), "component name should not be empty");

  exprt component;
  component.make_nil();

  PRECONDITION(
    op0.type().id() == ID_struct || op0.type().id() == ID_union ||
    op0.type().id() == ID_struct_tag || op0.type().id() == ID_union_tag);

  exprt member;

  if(get_component(expr.source_location(), op0, component_name, member))
  {
    // because of possible anonymous members
    expr.swap(member);
  }
  else
  {
    error().source_location = expr.find_source_location();
    error() << "member '" << component_name << "' of '" << to_string(type)
            << "' not found" << eom;
    throw 0;
  }

  add_implicit_dereference(expr);

  if(expr.type().id() == ID_code)
  {
    // Check if the function body has to be typechecked
    symbolt &component_symbol = symbol_table.get_writeable_ref(component_name);

    if(component_symbol.value.id() == ID_cpp_not_typechecked)
      component_symbol.value.set(ID_is_used, true);
  }
}

void cpp_typecheckt::typecheck_expr_ptrmember(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  PRECONDITION(expr.id() == ID_ptrmember);

  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "ptrmember operator expects one operand" << eom;
    throw 0;
  }

  auto &op = to_unary_expr(expr).op();

  add_implicit_dereference(op);

  // is operator-> overloaded?
  if(op.type().id() != ID_pointer)
  {
    std::string op_name = "operator->";

    const cpp_namet cpp_name(op_name, expr.source_location());

    side_effect_expr_function_callt function_call(
      cpp_name.as_expr(), {op}, uninitialized_typet{}, expr.source_location());

    typecheck_side_effect_function_call(function_call);

    already_typechecked_exprt::make_already_typechecked(function_call);

    op.swap(function_call);

    // Re-enter to handle the result (which may be a pointer or
    // another class with operator->).
    typecheck_expr_ptrmember(expr, fargs);
    return;
  }

  exprt tmp;
  op.swap(tmp);

  op.id(ID_dereference);
  op.add_to_operands(std::move(tmp));
  op.add_source_location() = expr.source_location();
  typecheck_expr_dereference(op);
  // a virtual pointer install of the complete object's constructor or
  // destructor (see get_component)
  if(expr.get_bool("#complete_object"))
    op.set("#complete_object", true);

  expr.id(ID_member);
  typecheck_expr_member(expr, fargs);
}

void cpp_typecheckt::typecheck_cast_expr(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "cast expressions expect one operand" << eom;
    throw 0;
  }

  exprt &cast_op = to_unary_expr(expr).op();

  add_implicit_dereference(cast_op);

  const irep_idt &id = expr.id();

  typet &type = expr.type();
  typecheck_type(type);

  source_locationt source_location = expr.source_location();

  exprt new_expr;
  if(id == ID_const_cast)
  {
    if(!const_typecast(cast_op, type, new_expr))
    {
      error().source_location = cast_op.find_source_location();
      error() << "type mismatch on const_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id == ID_dynamic_cast)
  {
    if(!dynamic_typecast(cast_op, type, new_expr))
    {
      error().source_location = cast_op.find_source_location();
      error() << "type mismatch on dynamic_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id == ID_reinterpret_cast)
  {
    if(!reinterpret_typecast(cast_op, type, new_expr))
    {
      error().source_location = cast_op.find_source_location();
      error() << "type mismatch on reinterpret_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id == ID_static_cast)
  {
    if(!static_typecast(cast_op, type, new_expr))
    {
      error().source_location = cast_op.find_source_location();
      error() << "type mismatch on static_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else
    UNREACHABLE;

  expr.swap(new_expr);
}

void cpp_typecheckt::typecheck_expr_cpp_name(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  source_locationt source_location = to_cpp_name(expr).source_location();

  if(expr.get_sub().size() == 1 && expr.get_sub()[0].id() == ID_name)
  {
    const irep_idt identifier = expr.get_sub()[0].get(ID_identifier);

    if(
      auto gcc_polymorphic = typecheck_gcc_polymorphic_builtin(
        identifier, fargs.operands, source_location))
    {
      // As the C front end does: one symbol per instantiated type, with an
      // implementation.  A single `__atomic_load_n' symbol shared by calls
      // on `long long*' and `int*' pointers (libstdc++'s
      // _Sp_counted_base::_M_release) had the return type of whichever
      // call came first, so the other call's result was of the wrong type
      // (--validate-goto-model: "function returns expression of wrong
      // type") and there was no body to execute.
      materialize_gcc_polymorphic_builtin(*gcc_polymorphic, source_location);
      expr = std::move(*gcc_polymorphic);
      return;
    }
  }

  for(std::size_t i = 0; i < expr.get_sub().size(); i++)
  {
    if(expr.get_sub()[i].id() == ID_cpp_name)
    {
      typet &type = static_cast<typet &>(expr.get_sub()[i]);
      typecheck_type(type);

      std::string tmp = "(" + cpp_type2name(type) + ")";

      typet name(ID_name);
      name.set(ID_identifier, tmp);
      name.add_source_location() = source_location;

      type = name;
    }
  }

  // N5008 [temp.names]/9: a concept-id is a prvalue of type bool;
  // [temp.constr.atomic]/3: if substituting its template arguments
  // yields an invalid type or expression, the constraint is NOT
  // SATISFIED -- the concept-id evaluates to `false`, it is not an
  // error.  libc++'s `same_as<_Tp, common_reference_t<_Tp, _Up>>`
  // (inside common_reference_with) relies on this for types with no
  // common_reference<...>::type.  Detect a concept-id by its base
  // name resolving to a concept template (the parser marks concept
  // declarators with `#concept`), evaluate under a SFINAE guard, and
  // fold failure to `false`.
  const bool is_concept_id = [&]() -> bool
  {
    const cpp_namet &cn = to_cpp_name(expr);
    if(!cn.has_template_args() || cn.is_qualified())
      return false;
    const auto ids = cpp_scopes.current_scope().lookup(
      cn.get_base_name(), cpp_scopet::RECURSIVE);
    for(const auto *idp : ids)
    {
      const symbolt *sym = symbol_table.lookup(idp->identifier);
      if(
        sym != nullptr && sym->type.get_bool(ID_is_template) &&
        sym->type.id() == ID_cpp_declaration)
      {
        const auto &decl = to_cpp_declaration(sym->type);
        if(
          !decl.declarators().empty() &&
          decl.declarators()[0].get_bool("#concept"))
          return true;
      }
    }
    return false;
  }();

  exprt symbol_expr;
  if(is_concept_id)
  {
    try
    {
      sfinae_contextt sfinae_guard{*this};
      symbol_expr =
        resolve(to_cpp_name(expr), cpp_typecheck_resolvet::wantt::VAR, fargs);
    }
    catch(...)
    {
      expr = false_exprt{};
      expr.add_source_location() = source_location;
      return;
    }
  }
  else
    symbol_expr =
      resolve(to_cpp_name(expr), cpp_typecheck_resolvet::wantt::VAR, fargs);

  // we want VAR
  CHECK_RETURN(symbol_expr.id() != ID_type);

  if(symbol_expr.id() == ID_member)
  {
    if(
      symbol_expr.operands().empty() ||
      to_multi_ary_expr(symbol_expr).op0().is_nil())
    {
      if(to_code_type(symbol_expr.type()).return_type().id() != ID_constructor)
      {
        if(cpp_scopes.current_scope().this_expr.is_nil())
        {
          if(symbol_expr.type().id() != ID_code)
          {
            error().source_location = source_location;
            error() << "object missing" << eom;
            throw 0;
          }

          // may still be good for address of
        }
        else
        {
          // Try again
          exprt ptrmem(ID_ptrmember);
          ptrmem.operands().push_back(cpp_scopes.current_scope().this_expr);

          ptrmem.add(ID_component_cpp_name) = expr;

          ptrmem.add_source_location() = source_location;
          typecheck_expr_ptrmember(ptrmem, fargs);
          symbol_expr.swap(ptrmem);
        }
      }
    }
  }
  else if(
    fargs.in_use && symbol_expr.id() == ID_symbol &&
    symbol_expr.type().id() == ID_code &&
    to_code_type(symbol_expr.type()).return_type().id() != ID_constructor &&
    !to_code_type(symbol_expr.type()).parameters().empty() &&
    to_code_type(symbol_expr.type()).parameters().front().get_this() &&
    cpp_scopes.current_scope().this_expr.is_not_nil())
  {
    // Instantiated template member function returned as symbol_exprt
    // when called from within a class method body. Build a member
    // expression with dereferenced 'this' as the object so that
    // typecheck_method_application adds the this argument.
    const exprt &this_expr = cpp_scopes.current_scope().this_expr;
    exprt object(ID_dereference, to_pointer_type(this_expr.type()).base_type());
    object.copy_to_operands(this_expr);
    object.type().set(
      ID_C_constant,
      to_pointer_type(this_expr.type()).base_type().get_bool(ID_C_constant));
    object.set(ID_C_lvalue, true);
    object.add_source_location() = source_location;

    exprt member(ID_member);
    member.set(ID_component_name, to_symbol_expr(symbol_expr).get_identifier());
    member.add_to_operands(std::move(object));
    member.type() = symbol_expr.type();
    member.add_source_location() = source_location;
    symbol_expr.swap(member);
  }

  symbol_expr.add_source_location() = source_location;
  expr = symbol_expr;

  if(expr.id() == ID_symbol)
    typecheck_expr_function_identifier(expr);
  else if(expr.id() == ID_member)
  {
    const irep_idt &component = expr.get(ID_component_name);
    // [basic.def.odr]/5: a member named in an unevaluated operand is not
    // odr-used, so its definition is not instantiated ([temp.inst]/4)
    if(!component.empty() && unevaluated_operand_depth == 0)
    {
      auto it = deferred_method_bodies.find(component);
      if(it != deferred_method_bodies.end())
      {
        method_bodies.push_back(std::move(it->second));
        deferred_method_bodies.erase(it);
      }
    }
  }

  add_implicit_dereference(expr);
}

void cpp_typecheckt::add_implicit_dereference(exprt &expr)
{
  if(is_reference(expr.type()) || is_rvalue_reference(expr.type()))
  {
    // add implicit dereference
    dereference_exprt tmp(expr);
    tmp.set(ID_C_implicit, true);
    tmp.add_source_location() = expr.source_location();
    tmp.set(ID_C_lvalue, true);
    expr.swap(tmp);
  }
}

exprt cpp_typecheckt::deduce_funcaddr_against_target(
  const exprt &name_or_addressof,
  const typet &target_fn_pointer_type)
{
  // Target must be pointer-to-code per [conv.func].  When the target
  // is a reference-to-function we could apply [temp.deduct.call]/3
  // forwarding-reference rules, but the conforming lvalue-to-rvalue
  // / function-to-pointer conversion sequence reduces those to the
  // same deduction.
  if(
    target_fn_pointer_type.id() != ID_pointer &&
    target_fn_pointer_type.id() != ID_frontend_pointer)
  {
    return nil_exprt{};
  }
  if(target_fn_pointer_type.get_sub().empty())
    return nil_exprt{};
  const typet &target_fn =
    static_cast<const typet &>(target_fn_pointer_type.get_sub().front());
  if(target_fn.id() != ID_code)
    return nil_exprt{};

  // Source shape: `&cpp_name` (explicit address-of of a name) or
  // plain `cpp_name` (implicit function-to-pointer per
  // [conv.func]/1).  Everything else is passed through to the
  // default resolve path so real type mismatches surface as
  // user-visible errors.
  exprt inner = name_or_addressof;
  bool had_address_of = false;
  if(inner.id() == ID_address_of)
  {
    had_address_of = true;
    if(inner.operands().size() != 1)
      return nil_exprt{};
    inner = to_unary_expr(inner).op();
  }
  if(inner.id() != ID_cpp_name)
    return nil_exprt{};

  // Build synthetic fargs matching the target function's parameter
  // list.  Per [temp.deduct.funcaddr]/1 these drive the
  // [temp.deduct.type] algorithm (13.10.3.6) to deduce the template
  // arguments that make P == A.
  const code_typet &target_code = to_code_type(target_fn);
  cpp_typecheck_fargst synth_fargs;
  synth_fargs.in_use = true;
  for(const auto &p : target_code.parameters())
  {
    symbol_exprt synth{"funcaddr_target_synth", p.type()};
    synth.set(ID_C_lvalue, true);
    synth_fargs.operands.push_back(synth);
  }

  try
  {
    exprt resolved = resolve(
      to_cpp_name(inner),
      cpp_typecheck_resolvet::wantt::VAR,
      synth_fargs,
      /*fail_with_exception=*/false);
    if(resolved.is_not_nil() && resolved.type().id() == ID_code)
    {
      // [conv.func]/1: function-to-pointer conversion is implicit
      // when the target context requires it; keep the `C_implicit`
      // marker iff the source wasn't an explicit `&`.
      address_of_exprt addr{resolved, pointer_type(resolved.type())};
      addr.add_source_location() = name_or_addressof.source_location();
      if(!had_address_of)
        addr.set(ID_C_implicit, true);
      return std::move(addr);
    }
  }
  catch(...)
  {
    // [temp.deduct]/8: substitution failure is silent; let the
    // default resolve path report the mismatch.
  }

  return nil_exprt{};
}

/// Phase 4 target-typet overload — pushes the target on the
/// call-target stack so that the no-target body's `fargs` carries
/// it through to the resolver and the conversion paths.
/// `fargs.target` is consulted by Phase 4B's [temp.deduct.conv]/1
/// implementation in `user_defined_conversion_sequence`.
void cpp_typecheckt::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr,
  const target_typet &target)
{
  call_target_stack.push_back(target);
  try
  {
    typecheck_side_effect_function_call(expr);
  }
  catch(...)
  {
    call_target_stack.pop_back();
    throw;
  }
  call_target_stack.pop_back();
}

// This function is currently 900+ lines.  Splitting it along the
// natural target-type boundaries (SystemC range handling, builtin
// dispatch, target-type-driven call resolution, per-argument
// conversion+rewriting) is tracked as a success criterion of the
// target-type-threading plan, see
// doc/architectural/cpp-frontend-plan-target-type-threading.md §7.6.
/// N5008 [class.copy.assign]/2: a class without a user-declared copy
/// assignment operator has one declared implicitly, and it can be named --
/// `_List_size::operator=(_List_size())' in libstdc++ 16's
/// _List_node_header::_M_init assigns the base subobject through it.  The
/// front end declares that operator only for non-POD classes (a POD is
/// assigned bitwise), so the qualified name found no function.  When \p expr
/// is a call `C::operator=(x)' with one argument, `C' a POD class without a
/// declared assignment operator and `this' available (a member function of
/// `C' or of a class derived from it), rewrite it to the builtin assignment
/// `static_cast<C &>(*this) = x' ([expr.ass]).
/// \return true when \p expr was rewritten
bool cpp_typecheckt::implicit_pod_assignment_call(
  side_effect_expr_function_callt &expr)
{
  if(expr.function().id() != ID_cpp_name || expr.arguments().size() != 1)
    return false;
  const irept::subt &subs = to_cpp_name(expr.function()).get_sub();
  if(
    subs.size() < 4 || subs[subs.size() - 2].id() != ID_operator ||
    subs.back().id() != "=" ||
    subs[subs.size() - 3].id() != ID_scope_resolution)
  {
    return false;
  }
  if(cpp_scopes.current_scope().this_expr.is_nil())
    return false;

  // the qualifier, `C'
  cpp_namet qualifier;
  qualifier.add(ID_C_source_location) = expr.function().source_location();
  for(std::size_t i = 0; i + 3 < subs.size(); ++i)
    qualifier.get_sub().push_back(subs[i]);
  exprt resolved;
  try
  {
    cpp_typecheck_fargst no_fargs;
    resolved = resolve(
      qualifier,
      cpp_typecheck_resolvet::wantt::TYPE,
      no_fargs,
      /*fail_with_exception=*/false);
  }
  catch(...)
  {
    return false;
  }
  if(
    resolved.id() != ID_type || resolved.type().id() != ID_struct_tag ||
    !cpp_is_pod(resolved.type()))
  {
    return false;
  }
  for(const auto &c :
      follow_tag(to_struct_tag_type(resolved.type())).components())
  {
    if(c.get_base_name() == "operator=")
      return false;
  }

  // static_cast<C &>(*this)
  exprt this_expr("cpp-this");
  this_expr.add_source_location() = expr.source_location();
  typecheck_expr(this_expr);
  exprt object{ID_dereference, typet{}};
  object.add_to_operands(already_typechecked_exprt{this_expr});
  object.add_source_location() = expr.source_location();
  typecheck_expr(object);
  object.set(ID_C_lvalue, true);
  exprt lhs{ID_static_cast, reference_type(resolved.type())};
  lhs.add_to_operands(already_typechecked_exprt{object});
  lhs.add_source_location() = expr.source_location();
  typecheck_expr(lhs);
  add_implicit_dereference(lhs);

  // (the argument was typechecked with the call; see
  // typecheck_side_effect_function_call)
  exprt rhs = expr.arguments().front();
  if(rhs.id() != ID_already_typechecked && rhs.type().is_not_nil())
    rhs = already_typechecked_exprt{rhs};
  side_effect_exprt assignment{
    ID_assign,
    {already_typechecked_exprt{lhs}, rhs},
    typet{},
    expr.source_location()};
  typecheck_expr(assignment);
  expr.swap(assignment);
  return true;
}

/// N5008 [lex.ext]/2-4: a user-defined-integer-literal (floating-point
/// literal) `nX' is a call of the literal operator `operator ""X' found by
/// unqualified lookup, in one of three forms: `operator ""X(n ULL)' if one
/// of them has a parameter of type unsigned long long (long double), else
/// `operator ""X("n")' for a raw literal operator (parameter `const char *')
/// or `operator ""X<'c1', ..., 'ck'>()' for a numeric literal operator
/// template ([over.literal]/5) -- libstdc++'s `12h' (chrono_literals).
/// The parser builds `operator ""X(n)' and records the literal's kind and
/// spelling; rewrite \p expr into the form the declarations found select.
/// Nothing is changed when none of the forms applies (the call then fails
/// to resolve, as [lex.ext]/3 requires a diagnostic).
void cpp_typecheckt::user_defined_numeric_literal(
  side_effect_expr_function_callt &expr)
{
  const irep_idt kind = expr.get("#user_defined_literal");
  if(kind.empty())
    return;
  const std::string spelling = expr.get_string("#literal_spelling");
  expr.remove("#user_defined_literal");
  expr.remove("#literal_spelling");
  if(
    expr.function().id() != ID_cpp_name || expr.arguments().size() != 1 ||
    spelling.empty())
  {
    return;
  }
  cpp_namet &name = to_cpp_name(expr.function());
  if(name.get_sub().size() != 2)
    return;
  const irep_idt base_name = "operator" + id2string(name.get_sub().back().id());

  const bool is_integer = kind == ID_integer;
  const typet cooked_type = is_integer ? typet{unsigned_long_long_int_type()}
                                       : typet{long_double_type()};
  bool has_cooked = false, has_raw = false, has_template = false;
  for(const auto &id :
      cpp_scopes.current_scope().lookup(base_name, cpp_scopet::RECURSIVE))
  {
    if(id->id_class == cpp_idt::id_classt::TEMPLATE)
    {
      has_template = true;
      continue;
    }
    const symbolt *symbol = symbol_table.lookup(id->identifier);
    if(symbol == nullptr || symbol->type.id() != ID_code)
      continue;
    const auto &parameters = to_code_type(symbol->type).parameters();
    if(parameters.size() != 1)
      continue;
    const typet &ptype = parameters.front().type();
    if(ptype == cooked_type)
      has_cooked = true;
    else if(
      ptype.id() == ID_pointer &&
      to_pointer_type(ptype).base_type().get_bool(ID_C_constant) &&
      to_pointer_type(ptype).base_type().id() == char_type().id() &&
      to_bitvector_type(to_pointer_type(ptype).base_type()).get_width() ==
        config.ansi_c.char_width)
    {
      has_raw = true;
    }
  }

  exprt &argument = expr.arguments().front();
  if(has_cooked)
  {
    // [lex.ext]/3-4: `n ULL', `f L' -- the literal itself, of that type
    exprt literal = argument;
    argument = typecast_exprt{literal, cooked_type};
    argument.add_source_location() = literal.source_location();
  }
  else if(has_raw && !has_template)
  {
    string_constantt raw{spelling};
    raw.add_source_location() = argument.source_location();
    argument = std::move(raw);
  }
  else if(has_template && !has_raw)
  {
    irept template_args{ID_template_args};
    irept &arguments = template_args.add(ID_arguments);
    for(const char c : spelling)
    {
      exprt character = from_integer(c, char_type());
      character.add_source_location() = argument.source_location();
      arguments.get_sub().push_back(std::move(character));
    }
    name.get_sub().push_back(std::move(template_args));
    expr.arguments().clear();
  }
}

void cpp_typecheckt::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr)
{
  user_defined_numeric_literal(expr);

  // A TYPELESS symbol as the callee is the synthesized body of a GCC
  // polymorphic builtin calling another one (`__atomic_load_n' calls
  // `__atomic_load', c_typecheck_gcc_polymorphic_builtins.cpp) or a CPROVER
  // primitive (`__CPROVER_atomic_begin'); the C front end resolves it in
  // typecheck_expr_symbol.  Hand it to the name path, which knows both
  // (typecheck_gcc_polymorphic_builtin, builtin_factory).
  if(
    expr.function().id() == ID_symbol &&
    (expr.function().type().is_nil() || expr.function().type().id().empty()))
  {
    const irep_idt &identifier =
      to_symbol_expr(expr.function()).get_identifier();
    if(!symbol_table.has_symbol(identifier))
    {
      cpp_namet name{identifier, expr.function().source_location()};
      expr.function() = name.as_expr();
    }
  }

  // N5008 [expr.type.conv]: a functional cast `T(args...)` whose T came
  // from substituting a template parameter is left by template_map::
  // apply as a function-call node whose CALLEE slot holds the RAW TYPE
  // (`A()` with A bound to int in `decltype(F()(A()...))`, the libc++
  // __invoke/__invokable chain under __range_adaptor_closure).  Rewrite
  // it to the explicit-constructor-call form the rest of the type
  // checker expects; otherwise the raw type node reaches expression
  // type-checking and fails with "unexpected expression: signedbv".
  if(
    expr.function().id() != ID_cpp_name && expr.function().id() != ID_symbol &&
    (expr.function().id() == ID_signedbv ||
     expr.function().id() == ID_unsignedbv ||
     expr.function().id() == ID_floatbv || expr.function().id() == ID_bool ||
     expr.function().id() == ID_c_bool || expr.function().id() == ID_pointer ||
     expr.function().id() == ID_struct_tag ||
     expr.function().id() == ID_union_tag ||
     expr.function().id() == ID_c_enum_tag))
  {
    exprt ctor_call("explicit-constructor-call");
    ctor_call.type() =
      static_cast<const typet &>(static_cast<const irept &>(expr.function()));
    ctor_call.operands() = expr.arguments();
    ctor_call.add_source_location() = expr.source_location();
    expr.swap(ctor_call);
    typecheck_expr(expr);
    return;
  }

  // For N5008 [class.inhctor.init]/1 (below): remember the NAME the call
  // was written with -- if it names class D but resolution selects an
  // INHERITED constructor (a base B's constructor made usable by a
  // using-declaration), the object to initialize is still a D, not a B.
  const exprt orig_function_name =
    expr.function().id() == ID_cpp_name ? expr.function() : nil_exprt();

  // [expr.call] re-entrant guard: when typechecking resumes on an
  // already-typechecked subexpression — e.g., when
  // `cpp_constructor`'s operand loop calls `typecheck_expr` on an
  // existing `*move(...)` and the operand walk descends back into
  // the inner side-effect-call — the call has already had its
  // function operand resolved (`expr.function()` is a `symbol_expr`
  // pointing at the instantiated function template) and its
  // return type set to a reference (`T&` / `T&&`).  Re-running the
  // body would call `add_implicit_dereference(expr)` at the tail
  // again, wrapping the call in a SECOND `*` and corrupting the
  // parent dereference into `*(*call(...))`.
  // `typecheck_expr_dereference` would then reject the outer
  // dereference's operand as
  //   operand of unary * is not a pointer, but got 'struct T'
  // — which surfaces in libstdc++ chains as
  //   *move<ref_struct_tag(identifier=tag-X)>(...)
  // is not a pointer.  Detect this specific shape — a call already
  // resolved to a symbol AND whose return type is a reference —
  // and short-circuit.
  if(
    expr.function().id() == ID_symbol &&
    expr.function().type().id() == ID_code &&
    (is_reference(expr.type()) || is_rvalue_reference(expr.type())))
  {
    return;
  }

  // [meta.const.eval]/1 with [expr.const]: __builtin_is_constant_evaluated()
  // yields true if and only if it is evaluated within a manifestly
  // constant-evaluated context, and false otherwise.  The front-end tracks
  // such contexts with constant_expression_context (incremented while
  // type-checking constant expressions / constexpr-required contexts, and
  // reset to 0 by non_constant_expression_contextt while elaborating ordinary
  // run-time function bodies).
  //
  // While in a constant-evaluated context, fold to true.  Otherwise --
  // crucially
  // -- do NOT fold to false here; leave the call in place.  Folding to false at
  // type-check time would bake a run-time answer into any function body that
  // forwards the built-in (e.g. std::is_constant_evaluated /
  // std::__is_constant_evaluated, whose bodies are `return
  // __builtin_is_constant_evaluated();`), making the wrapper non-context-
  // dependent.  Left in place, the call is re-folded to true when such a body
  // is nested-evaluated during constant evaluation, and otherwise falls through
  // at run time to the built-in's definition (see cpp_internal_additions),
  // which returns false -- exactly what symex must observe.  Both the
  // unresolved (cpp_name) and resolved (symbol) forms are handled, the latter
  // arising when a forwarding body is re-evaluated by the constexpr evaluator.
  {
    bool is_ice_builtin = false;
    if(expr.function().id() == ID_cpp_name)
    {
      is_ice_builtin = to_cpp_name(expr.function()).get_base_name() ==
                       "__builtin_is_constant_evaluated";
    }
    else if(expr.function().id() == ID_symbol)
    {
      is_ice_builtin = has_prefix(
        id2string(to_symbol_expr(expr.function()).get_identifier()),
        "__builtin_is_constant_evaluated");
    }

    if(is_ice_builtin && constant_expression_context > 0)
    {
      exprt result = true_exprt{};
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
  }

  if(expr.function().id() == ID_cpp_name)
  {
    const auto &name = to_cpp_name(expr.function());
    const irep_idt &bn = name.get_base_name();
    // Clang's library-support intrinsics: per clang's documentation
    // __builtin_operator_new/__builtin_operator_delete behave exactly
    // like a call to '::operator new(args)' / '::operator delete(args)'
    // (N5008 [new.delete.single]: operator new returns a non-null
    // pointer to storage of the requested size, or throws; operator
    // delete deallocates).  They have no declaration the C++ resolver
    // could find (libc++'s __libcpp_operator_new forwards a variadic
    // pack to them), so intercept the calls directly: model the
    // allocation with CBMC's allocator and the deallocation as a no-op,
    // exactly like the provide_stdlib_bodies model for
    // __libcpp_operator_new.
    if(bn == "__builtin_operator_new" && !expr.arguments().empty())
    {
      exprt size_arg = expr.arguments().front();
      typecheck_expr(size_arg);
      side_effect_exprt alloc{
        ID_allocate,
        {std::move(size_arg), false_exprt()},
        pointer_type(empty_typet{}),
        expr.source_location()};
      expr.swap(alloc);
      return;
    }
    if(bn == "__builtin_operator_delete")
    {
      for(auto &arg : expr.arguments())
        typecheck_expr(arg);
      exprt nil = nil_exprt{};
      exprt as_void("already_typechecked");
      // no-op: evaluate to a void constant expression
      exprt result = exprt(ID_nil);
      code_skipt skip;
      exprt void_expr(ID_side_effect, empty_typet{});
      void_expr.set(ID_statement, ID_skip);
      void_expr.add_source_location() = expr.source_location();
      expr.swap(void_expr);
      return;
    }
    // GCC/Clang __builtin_launder(p), the built-in behind std::launder:
    // N5008 [ptr.launder]/1-3, the result is a pointer to the object that p
    // points to, i.e. it has p's value and type; the program is ill-formed
    // if the pointee is a function type or cv void.  Type-generic, so it has
    // no declaration the resolver could find.
    if(bn == "__builtin_launder")
    {
      if(expr.arguments().size() != 1)
      {
        error().source_location = expr.source_location();
        error() << "__builtin_launder expects one argument" << eom;
        throw 0;
      }
      exprt arg = expr.arguments().front();
      typecheck_expr(arg);
      // [conv.array], [conv.func]: the argument is a prvalue pointer
      add_implicit_dereference(arg);
      if(arg.type().id() == ID_array)
        implicit_typecast(
          arg, pointer_type(to_array_type(arg.type()).element_type()));
      if(
        arg.type().id() != ID_pointer ||
        to_pointer_type(arg.type()).base_type().id() == ID_code ||
        to_pointer_type(arg.type()).base_type().id() == ID_empty)
      {
        error().source_location = expr.source_location();
        error() << "__builtin_launder expects a pointer to an object type"
                << eom;
        throw 0;
      }
      arg.remove(ID_C_lvalue);
      arg.add_source_location() = expr.source_location();
      expr.swap(arg);
      return;
    }
    // Clang's __builtin_popcountg(x) (clang 19+, and GCC 14): the number of
    // 1 bits of an unsigned integer of any width, as an int (Clang "Language
    // Extensions"); usable in constant expressions, where libc++ 23's
    // numeric_limits computes `digits' with it.
    if(bn == "__builtin_popcountg")
    {
      if(expr.arguments().size() != 1)
      {
        error().source_location = expr.source_location();
        error() << "__builtin_popcountg expects one argument" << eom;
        throw 0;
      }
      exprt arg = expr.arguments().front();
      typecheck_expr(arg);
      add_implicit_dereference(arg);
      if(arg.type().id() != ID_unsignedbv)
      {
        error().source_location = expr.source_location();
        error() << "__builtin_popcountg expects an unsigned integer argument"
                << eom;
        throw 0;
      }
      popcount_exprt result{arg, signed_int_type()};
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
    // GCC's __builtin_shuffle and Clang's __builtin_shufflevector (vector
    // extensions, no N5008 counterpart): type-generic, so there is no
    // declaration to resolve; the arguments are type-checked here and the
    // C front end's implementation builds the shuffle
    if(bn == "__builtin_shuffle" || bn == "__builtin_shufflevector")
    {
      side_effect_expr_function_callt call = expr;
      for(auto &arg : call.arguments())
      {
        typecheck_expr(arg);
        add_implicit_dereference(arg);
      }
      call.function() = symbol_exprt{bn, typet{}};
      call.function().add_source_location() = expr.source_location();
      exprt result = typecheck_shuffle_vector(call);
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
    // GCC built-in floating-point classification
    if(
      (bn == "__builtin_isfinite" || bn == "__builtin_isinf" ||
       bn == "__builtin_isnan" || bn == "__builtin_isnormal") &&
      expr.arguments().size() == 1)
    {
      typecheck_expr(expr.arguments()[0]);
      exprt arg = expr.arguments()[0];
      exprt result;
      if(bn == "__builtin_isfinite")
        result = isfinite_exprt(arg);
      else if(bn == "__builtin_isinf")
        result = isinf_exprt(arg);
      else if(bn == "__builtin_isnan")
        result = isnan_exprt(arg);
      else
        result = isnormal_exprt(arg);
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
  }

  // For virtual functions, it is important to check whether
  // the function name is qualified. If it is qualified, then
  // the call is not virtual.
  bool is_qualified = false;

  if(expr.function().id() == ID_member || expr.function().id() == ID_ptrmember)
  {
    if(expr.function().get(ID_component_cpp_name) == ID_cpp_name)
    {
      const cpp_namet &cpp_name =
        to_cpp_name(expr.function().find(ID_component_cpp_name));
      is_qualified = cpp_name.is_qualified();
    }
  }
  else if(expr.function().id() == ID_cpp_name)
  {
    const cpp_namet &cpp_name = to_cpp_name(expr.function());
    is_qualified = cpp_name.is_qualified();
  }

  // Backup of the original operand
  exprt op0 = expr.function();

  // Pre-typecheck arguments to get their types for template argument
  // deduction. This is needed for function templates with partial
  // explicit template arguments (e.g., duration_cast<seconds>(d)).
  for(auto &arg : expr.arguments())
  {
    // N5008 [class.access.general]/5: access control for a name is
    // judged in the context in which the name APPEARS.  The elements of
    // a braced-init-list argument (`wrapt w({this->member})`) are
    // expressions of the call site; typecheck them HERE, in the calling
    // member's scope, and mark them done.  Deferring them to the
    // conversion machinery (which runs during overload resolution with
    // a different current scope) mis-judged the enclosing class's own
    // private members as inaccessible.
    if(arg.id() == ID_initializer_list)
    {
      for(auto &element : arg.operands())
      {
        if(
          element.id() == ID_initializer_list ||
          element.id() == ID_already_typechecked ||
          (!element.type().id().empty() && !element.type().is_nil()))
        {
          continue; // nested lists keep their target-dependent handling
        }
        try
        {
          exprt tmp = element;
          typecheck_expr(tmp);
          // Expose the element's type on the wrapper so candidate
          // matching (brace_init_is_viable, fargs) sees it; the later
          // unwrap in typecheck_expr is unaffected.
          typet element_type = tmp.type();
          already_typechecked_exprt::make_already_typechecked(tmp);
          tmp.type() = std::move(element_type);
          element.swap(tmp);
        }
        catch(...)
        {
          // leave the element for the conversion machinery
        }
      }
      continue;
    }
    if(arg.type().id().empty() || arg.type().is_nil())
    {
      // [temp.deduct.funcaddr]: an argument of the form `&f` or
      // just `f` where `f` names a function template cannot be
      // typechecked in isolation — the deduction requires the
      // target parameter type of the outer call.  Defer this arg
      // to the post-function-resolution retry pass below so its
      // failure here doesn't abort the whole expression.
      bool is_funcaddr_template_candidate = false;
      {
        const exprt *probe = &arg;
        if(probe->id() == ID_address_of && probe->operands().size() == 1)
          probe = &to_unary_expr(*probe).op();
        if(probe->id() == ID_cpp_name)
          is_funcaddr_template_candidate = true;
      }
      if(is_funcaddr_template_candidate)
        continue;

      try
      {
        typecheck_expr(arg);
      }
      catch(...)
      {
        // ignore errors — argument may depend on template resolution
      }
    }
  }

  // now do the function -- this has been postponed
  // SystemC extension: a.range(upper, lower) on bitvector types
  if(
    expr.function().id() == ID_member &&
    expr.function().find(ID_component_cpp_name).is_not_nil() &&
    expr.arguments().size() == 2)
  {
    const cpp_namet &member_name =
      to_cpp_name(expr.function().find(ID_component_cpp_name));
    const irep_idt &base = member_name.get_base_name();
    if(base == "range")
    {
      exprt &obj = to_unary_expr(expr.function()).op();
      typecheck_expr(obj);
      add_implicit_dereference(obj);
      if(obj.type().id() == ID_unsignedbv)
      {
        typecheck_expr(expr.arguments()[0]);
        typecheck_expr(expr.arguments()[1]);
        const auto upper = numeric_cast<mp_integer>(expr.arguments()[0]);
        const auto lower = numeric_cast<mp_integer>(expr.arguments()[1]);
        if(upper.has_value() && lower.has_value() && *upper >= *lower)
        {
          const std::size_t width =
            numeric_cast_v<std::size_t>(*upper - *lower + 1);
          extractbits_exprt result(
            obj,
            from_integer(*lower, unsignedbv_typet(32)),
            unsignedbv_typet(width));
          result.add_source_location() = expr.source_location();
          expr.swap(result);
          return;
        }
      }
    }
  }

  // Forward-deduce template-function-address arguments against
  // target parameter types per [temp.deduct.funcaddr]/1.  Probe the
  // callee to obtain its parameter types (when resolvable without
  // fargs); for each deferred argument that's a `cpp_name` /
  // `&cpp_name`, retry the typecheck with the matching parameter as
  // the target, which routes to `deduce_funcaddr_against_target`
  // via `typecheck_expr(exprt &, const target_typet &)`.
  if(expr.function().id() == ID_cpp_name && !expr.arguments().empty())
  {
    bool any_deferred = false;
    for(const auto &a : expr.arguments())
      if(a.type().is_nil() || a.type().id().empty())
      {
        any_deferred = true;
        break;
      }

    if(any_deferred)
    {
      cpp_typecheck_fargst probe_fargs;
      exprt probe_fn = expr.function();
      try
      {
        probe_fn = resolve(
          to_cpp_name(probe_fn),
          cpp_typecheck_resolvet::wantt::VAR,
          probe_fargs,
          /*fail_with_exception=*/false);
      }
      catch(...)
      {
        probe_fn.make_nil();
      }

      if(probe_fn.is_not_nil() && probe_fn.type().id() == ID_code)
      {
        const auto &params = to_code_type(probe_fn.type()).parameters();
        for(std::size_t i = 0; i < params.size() && i < expr.arguments().size();
            ++i)
        {
          exprt &arg = expr.arguments()[i];
          if(!arg.type().is_nil() && !arg.type().id().empty())
            continue;

          typecheck_expr(arg, target_typet{params[i].type()});
        }
      }
    }
  }

  // Build fargs for overload resolution.  Carry the active target
  // type from the call-target stack so the resolver and conversion
  // paths can use it to drive [temp.deduct.conv]/1 deduction (see
  // Phase 4B in the target-type-threading plan).  The stack is set
  // by the `typecheck_side_effect_function_call(exprt &,
  // const target_typet &)` overload.
  // N5008 [over.match.class.deduct]: `C(args)` where C names a class template
  // written without a template-argument-list is class template argument
  // deduction (CTAD), not a function call.  The parser cannot tell C is a type
  // (it is only a template-name), so it emits a function call; re-route it to
  // the explicit-constructor-call / CTAD path here (deduce_class_template_
  // arguments returns nullopt for anything that is not a class template, so an
  // ordinary function call falls through).  Without this, `std::optional(x)`
  // and similar failed with "found no match for C".
  if(expr.function().id() == ID_cpp_name)
  {
    const cpp_namet &fn_name = to_cpp_name(expr.function());
    if(deduce_class_template_arguments(fn_name, expr.arguments()).has_value())
    {
      exprt ctor_call("explicit-constructor-call");
      ctor_call.type() =
        static_cast<const typet &>(static_cast<const irept &>(fn_name));
      ctor_call.operands() = expr.arguments();
      // arguments this route has already type-checked (e.g. through the
      // call-target loop above) must not be type-checked again: a
      // lowered aggregate VALUE (struct_exprt) has no second-round
      // handler ("unexpected expression: struct", the braced
      // base-element CTAD shape)
      for(auto &a : ctor_call.operands())
      {
        if(a.type().is_not_nil() && !a.type().id().empty())
          already_typechecked_exprt::make_already_typechecked(a);
      }
      ctor_call.add_source_location() = expr.source_location();
      typecheck_expr_explicit_constructor_call(ctor_call);
      expr.swap(ctor_call);
      return;
    }
  }

  // N5008 [expr.type.conv]/1.1: with a single parenthesized expression the
  // functional cast `T(e)' is equivalent to the cast expression `(T)e'
  // ([expr.cast]/4: a static_cast, reinterpret_cast or const_cast).  A
  // simple-type-specifier (`long(p)') is parsed as a cast already; a
  // typedef-name or template parameter naming a non-class type (`U(p)',
  // libstdc++'s `uintptr_t(__addr)') reaches here as a call, and the
  // pseudo-constructor of the resolver would only admit implicit
  // conversions.
  if(
    expr.function().id() == ID_cpp_name && expr.arguments().size() == 1 &&
    expr.arguments().front().id() != ID_initializer_list &&
    expr.arguments().front().type().is_not_nil())
  {
    cpp_typecheck_fargst no_fargs;
    exprt type_expr = nil_exprt{};
    {
      sfinae_contextt probe{*this};
      try
      {
        type_expr = resolve(
          to_cpp_name(expr.function()),
          cpp_typecheck_resolvet::wantt::TYPE,
          no_fargs,
          false);
      }
      catch(...)
      {
        type_expr = nil_exprt{};
      }
    }
    if(type_expr.id() == ID_type)
    {
      const typet &target = type_expr.type();
      const irep_idt &tid = target.id();
      const bool scalar = tid == ID_signedbv || tid == ID_unsignedbv ||
                          tid == ID_bool || tid == ID_c_bool ||
                          tid == ID_floatbv || tid == ID_c_enum_tag ||
                          (tid == ID_pointer && !is_reference(target) &&
                           !is_rvalue_reference(target));
      if(scalar)
      {
        exprt typecast("explicit-typecast");
        typecast.type() = target;
        typecast.add_source_location() = expr.source_location();
        typecast.copy_to_operands(expr.arguments().front());
        typecheck_expr_explicit_typecast(typecast);
        expr.swap(typecast);
        return;
      }
    }
  }

  // N5008 [expr.type.conv]/2 + [over.match.copy]/1.2: the functional cast
  // `T(x)' -- T a class type, x of ANOTHER class type -- is a
  // direct-initialization in which an EXPLICIT conversion function of x's
  // class yielding T is a candidate for the temporary bound to the
  // copy/move constructor's `T&' parameter (libstdc++ 16's
  // `const_iterator(__loc)' with `explicit operator const_iterator()' and
  // `explicit operator iterator()' on _Hashtable::__location_type).
  // Implicit conversion sequences never use explicit conversion functions
  // ([class.conv.fct]/2), so constructor resolution below either finds no
  // candidate or -- taking every conversion function as implicit -- an
  // ambiguity between the copy constructor and `const_iterator(const
  // iterator&)'.  Convert x with that function; the copy/move is elided
  // ([class.copy.elision]/1).
  if(
    expr.function().id() == ID_cpp_name && expr.arguments().size() == 1 &&
    expr.arguments().front().type().is_not_nil())
  {
    const exprt &arg = expr.arguments().front();
    typet arg_type = arg.type();
    if(is_reference(arg_type) || is_rvalue_reference(arg_type))
      arg_type = to_pointer_type(arg_type).base_type();
    if(arg_type.id() == ID_struct_tag)
    {
      // does the name denote a class type?  (a function template such as
      // `std::forward<Args>' is not one; its failure to resolve as a type
      // is no error here)
      cpp_typecheck_fargst no_fargs;
      exprt type_expr = nil_exprt{};
      {
        // a probe: no diagnostics ([temp.deduct]/8-style soft failure)
        sfinae_contextt probe{*this};
        try
        {
          type_expr = resolve(
            to_cpp_name(expr.function()),
            cpp_typecheck_resolvet::wantt::TYPE,
            no_fargs,
            false);
        }
        catch(...)
        {
          type_expr = nil_exprt{};
        }
      }
      exprt converted;
      if(
        type_expr.id() == ID_type && type_expr.type().id() == ID_struct_tag &&
        to_struct_tag_type(type_expr.type()).get_identifier() !=
          to_struct_tag_type(arg_type).get_identifier() &&
        explicit_conversion_function_to(arg, type_expr.type(), converted))
      {
        converted.add_source_location() = expr.source_location();
        expr.swap(converted);
        return;
      }
    }
  }

  cpp_typecheck_fargst call_fargs(expr);
  if(!call_target_stack.empty())
    call_fargs.target = call_target_stack.back();
  const std::size_t errors_before_function_expr =
    get_message_handler().get_message_count(messaget::M_ERROR);
  try
  {
    typecheck_function_expr(expr.function(), call_fargs);
  }
  catch(...)
  {
    if(implicit_pod_assignment_call(expr))
    {
      get_message_handler().set_message_count(
        messaget::M_ERROR, errors_before_function_expr);
      return;
    }
    // C++20 P0960 (N5008 [expr.type.conv]/2 +
    // [dcl.init.general]/16.6.2.2): constructors are considered first;
    // when overload resolution finds no viable constructor and
    // `T(args)` names an AGGREGATE class type, the expression-list
    // initializes the aggregate's elements.  Retry through the
    // explicit-constructor-call path, whose aggregate fallback
    // implements this.  libstdc++'s C++20 forward_as_tuple body
    // (`tuple<_Elements...>(__args...)`) was dropped without it,
    // losing std::map's piecewise-constructed key.  Guarded against
    // re-entry: the retry's own constructor-first attempt goes through
    // cpp_constructor, whose synthesized call must not re-reroute.
    if(
      config.cpp.cpp_standard < configt::cppt::cpp_standardt::CPP20 ||
      expr.function().id() != ID_cpp_name || expr.arguments().empty())
      throw;
    exprt type_probe;
    try
    {
      cpp_typecheck_fargst no_fargs;
      type_probe = resolve(
        to_cpp_name(expr.function()),
        cpp_typecheck_resolvet::wantt::TYPE,
        no_fargs,
        /*fail_with_exception=*/false);
    }
    catch(...)
    {
      type_probe.make_nil();
    }
    if(type_probe.id() != ID_type || type_probe.type().id() != ID_struct_tag)
      throw;
    const struct_typet &probe_struct =
      follow_tag(to_struct_tag_type(type_probe.type()));
    bool user_ctor = probe_struct.get_bool("has_template_constructor") ||
                     probe_struct.get_bool("has_inherited_constructor") ||
                     probe_struct.is_incomplete();
    for(const auto &c : probe_struct.components())
    {
      if(
        user_ctor || c.type().id() != ID_code || c.get_bool(ID_from_base) ||
        to_code_type(c.type()).return_type().id() != ID_constructor)
        continue;
      if(!c.type().get_bool("#is_implicit_ctor"))
        user_ctor = true;
    }
    const irep_idt probe_id =
      to_struct_tag_type(type_probe.type()).get_identifier();
    if(user_ctor || !paren_aggregate_in_progress.insert(probe_id).second)
      throw;
    struct guardt
    {
      std::set<irep_idt> &set;
      irep_idt id;
      ~guardt()
      {
        set.erase(id);
      }
    } guard{paren_aggregate_in_progress, probe_id};
    get_message_handler().set_message_count(
      messaget::M_ERROR, errors_before_function_expr);
    exprt ctor_call("explicit-constructor-call");
    ctor_call.type() = type_probe.type();
    ctor_call.operands() = expr.arguments();
    ctor_call.add_source_location() = expr.source_location();
    typecheck_expr_explicit_constructor_call(ctor_call);
    expr.swap(ctor_call);
    return;
  }

  if(expr.function().id() == ID_pod_constructor)
  {
    PRECONDITION(expr.function().type().id() == ID_code);

    // This should be a POD, but in partially-elaborated template
    // instances (where our self-reference tolerance in
    // typecheck_compound_type left an unresolved cpp_name member
    // type) the pod_constructor tag can outlive the POD-ness of
    // the return type.  Fall back to a plain typecast / default
    // initialization rather than tripping a precondition and
    // crashing with an invariant violation.
    const typet &pod = to_code_type(expr.function().type()).return_type();
    if(!cpp_is_pod(pod))
    {
      if(expr.arguments().size() <= 1)
      {
        exprt typecast("explicit-typecast");
        typecast.type() = pod;
        typecast.add_source_location() = expr.source_location();
        if(!expr.arguments().empty())
          typecast.copy_to_operands(expr.arguments().front());
        typecheck_expr_explicit_typecast(typecast);
        expr.swap(typecast);
        return;
      }
      error().source_location = expr.source_location();
      error() << "zero or one argument expected" << eom;
      throw 0;
    }

    // These aren't really function calls, but either conversions or
    // initializations.
    if(expr.arguments().size() <= 1)
    {
      exprt typecast("explicit-typecast");
      typecast.type() = pod;
      typecast.add_source_location() = expr.source_location();
      if(!expr.arguments().empty())
        typecast.copy_to_operands(expr.arguments().front());
      typecheck_expr_explicit_typecast(typecast);
      expr.swap(typecast);
    }
    else
    {
      error().source_location = expr.source_location();
      error() << "zero or one argument expected" << eom;
      throw 0;
    }

    return;
  }
  else if(expr.function().id() == ID_cpp_dummy_destructor)
  {
    // these don't do anything, e.g., (char*)->~char()
    typecast_exprt no_op(from_integer(0, signed_int_type()), void_type());
    expr.swap(no_op);
    return;
  }

  // look at type of function

  // N5008 [expr.call]/1, [over.call.object]: when the postfix-expression
  // denoting the callee is a reference (e.g. the result of
  // `static_cast<F&&>(f)` / `std::forward<F>(f)`, modelled here as a pointer
  // carrying the reference flag), it is bound to its referand; the call is on
  // the referand object.  Dereference it to that lvalue so a class type with
  // an `operator()` routes to the operator() resolution below instead of being
  // mistaken for a function pointer (which derefs once and then reports
  // "expecting code as argument").  A plain reference *parameter* already
  // yields a referand lvalue, so this only affects reference-typed callee
  // expressions; non-reference function pointers are unaffected.
  add_implicit_dereference(expr.function());

  if(expr.function().type().id() == ID_pointer)
  {
    if(expr.function().type().find(ID_to_member).is_not_nil())
    {
      const exprt &bound =
        static_cast<const exprt &>(expr.function().type().find(ID_C_bound));

      if(bound.is_nil())
      {
        error().source_location = expr.source_location();
        error() << "pointer-to-member not bound" << eom;
        throw 0;
      }

      // add `this'
      DATA_INVARIANT(bound.type().id() == ID_pointer, "should be pointer");
      expr.arguments().insert(expr.arguments().begin(), bound);

      // we don't need the object any more
      expr.function().type().remove(ID_C_bound);
    }

    // do implicit dereference
    if(expr.function().id() == ID_address_of)
    {
      exprt tmp;
      tmp.swap(to_address_of_expr(expr.function()).object());
      expr.function().swap(tmp);
    }
    else
    {
      PRECONDITION(expr.function().type().id() == ID_pointer);
      dereference_exprt tmp(expr.function());
      tmp.add_source_location() = expr.function().source_location();
      expr.function().swap(tmp);
    }

    if(expr.function().type().id() != ID_code)
    {
      error().source_location = expr.function().find_source_location();
      error() << "expecting code as argument" << eom;
      throw 0;
    }
  }
  else if(expr.function().type().id() == ID_code)
  {
    if(expr.function().type().get_bool(ID_C_is_virtual) && !is_qualified)
    {
      exprt vtptr_member;
      if(op0.id() == ID_member || op0.id() == ID_ptrmember)
      {
        vtptr_member.id(op0.id());
        vtptr_member.add_to_operands(std::move(to_unary_expr(op0).op()));
      }
      else
      {
        vtptr_member.id(ID_ptrmember);
        exprt this_expr("cpp-this");
        vtptr_member.add_to_operands(std::move(this_expr));
      }

      // get the virtual table
      auto this_type = to_pointer_type(
        to_code_type(expr.function().type()).parameters().front().type());

      const struct_typet &vt_struct =
        follow_tag(to_struct_tag_type(this_type.base_type()));

      // Find the vtable struct holding the called function's slot and the
      // vtable pointer to reach it.  The slot lives in the vtable struct of
      // the class that declares the function (its base_name is the
      // function's virtual-name).  Itanium C++ ABI 2.4 II.1: a class with a
      // primary base shares that base's virtual pointer, and its own vtable
      // struct embeds the primary base's as first member `@base'; so the
      // pointer to dispatch through is the one of the primary-base chain
      // (vtable_pointer_component), cast to the declaring class's vtable
      // struct.  A class with several dynamic non-primary bases has several
      // pointers; the one whose chain holds the slot is the one to use.
      const irep_idt virtual_name =
        expr.function().type().get(ID_C_virtual_name);
      const irep_idt declaring_class = this_type.base_type().get(ID_identifier);
      const irep_idt vt_name = "virtual_table::" + id2string(declaring_class);
      irep_idt vtptr_name = vtable_pointer_component(declaring_class);
      irep_idt slot_vt_name = vt_name;
      const auto vt_has_entry = [this, &virtual_name](const irep_idt &vt_id)
      {
        const symbolt *vt_sym = symbol_table.lookup(vt_id);
        if(vt_sym == nullptr || vt_sym->type.id() != ID_struct)
          return false;
        for(const auto &entry : to_struct_type(vt_sym->type).components())
          if(entry.get_base_name() == virtual_name)
            return true;
        return false;
      };
      if(vtptr_name.empty() || !vt_has_entry(vt_name))
      {
        // fall back to a vtable pointer of the class whose vtable struct
        // has the entry
        vtptr_name.clear();
        for(const auto &c : vt_struct.components())
        {
          if(!c.get_bool(ID_is_vtptr))
            continue;
          const typet &vt_tag = to_pointer_type(c.type()).base_type();
          if(vt_tag.id() != ID_struct_tag)
            continue;
          const irep_idt candidate =
            to_struct_tag_type(vt_tag).get_identifier();
          if(vtptr_name.empty())
          {
            vtptr_name = c.get_name();
            slot_vt_name = candidate;
          }
          if(vt_has_entry(candidate))
          {
            vtptr_name = c.get_name();
            slot_vt_name = candidate;
            break;
          }
        }
      }
      CHECK_RETURN(!vtptr_name.empty());

      vtptr_member.set(ID_component_name, vtptr_name);
      typecheck_expr(vtptr_member);

      // the shared pointer has the primary-base chain's static type; view it
      // as a pointer to the declaring class's vtable struct
      const pointer_typet slot_vt_pointer =
        pointer_type(struct_tag_typet(slot_vt_name));
      if(vtptr_member.type() != slot_vt_pointer)
      {
        vtptr_member = typecast_exprt(vtptr_member, slot_vt_pointer);
      }
      already_typechecked_exprt::make_already_typechecked(vtptr_member);

      // look for the right entry
      irep_idt vtentry_component_name =
        id2string(slot_vt_name) +
        "::" + expr.function().type().get_string(ID_C_virtual_name);

      exprt vtentry_member(ID_ptrmember);
      vtentry_member.copy_to_operands(vtptr_member);
      vtentry_member.set(ID_component_name, vtentry_component_name);
      typecheck_expr(vtentry_member);

      CHECK_RETURN(vtentry_member.type().id() == ID_pointer);

      {
        dereference_exprt tmp(vtentry_member);
        tmp.add_source_location() = expr.function().source_location();
        vtentry_member.swap(tmp);
      }

      // Typecheck the expression as if it was not virtual
      // (add the this pointer)

      expr.type() = to_code_type(expr.function().type()).return_type();

      if(expr.function().id() == ID_member)
        typecheck_method_application(expr);

      // Let's make the call virtual
      expr.function().swap(vtentry_member);

      typecheck_function_call_arguments(expr);
      add_implicit_dereference(expr);
      return;
    }
  }
  else if(expr.function().type().id() == ID_struct_tag)
  {
    const cpp_namet cppname("operator()", expr.source_location());

    // The function expression evaluates to a struct value (e.g., F()).
    // Wrap it in a temporary_object so the this pointer can be formed.
    exprt obj = std::move(expr.function());
    if(!obj.get_bool(ID_C_lvalue))
    {
      side_effect_exprt tmp(
        ID_temporary_object, obj.type(), obj.source_location());
      tmp.add_to_operands(std::move(obj));
      tmp.set(ID_C_lvalue, true);
      tmp.set(ID_mode, ID_cpp);
      obj = std::move(tmp);
    }

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cppname;
    member.add_to_operands(already_typechecked_exprt{std::move(obj)});

    expr.function().swap(member);
    typecheck_side_effect_function_call(expr);

    return;
  }
  else
  {
    error().source_location = expr.function().find_source_location();
    error() << "function call expects function or function "
            << "pointer as argument, but got '"
            << to_string(expr.function().type()) << "'" << eom;
    throw 0;
  }

  expr.type() = to_code_type(expr.function().type()).return_type();

  if(expr.type().id() == ID_constructor)
  {
    PRECONDITION(expr.function().id() == ID_symbol);

    const code_typet::parameterst &parameters =
      to_code_type(expr.function().type()).parameters();

    DATA_INVARIANT(!parameters.empty(), "parameters expected");

    const auto &this_type = to_pointer_type(parameters[0].type());

    // change type from 'constructor' to object type
    expr.type() = this_type.base_type();

    // create temporary object
    side_effect_exprt tmp_object_expr(
      ID_temporary_object, this_type.base_type(), expr.source_location());
    tmp_object_expr.set(ID_C_lvalue, true);
    tmp_object_expr.set(ID_mode, ID_cpp);

    exprt member;

    exprt new_object(ID_new_object, tmp_object_expr.type());
    new_object.set(ID_C_lvalue, true);

    PRECONDITION(
      tmp_object_expr.type().id() == ID_struct_tag ||
      tmp_object_expr.type().id() == ID_union_tag);

    const bool component_found = get_component(
      expr.source_location(),
      new_object,
      expr.function().get(ID_identifier),
      member);
    if(!component_found)
    {
      // The selected constructor is not among the class's components --
      // e.g. its registration was skipped during a partial elaboration
      // (an extern-template'd member of a class whose other members
      // mention still-incomplete types).  Proceeding would swap a
      // non-member expression into the call and abort
      // typecheck_method_application's precondition.  Fail the
      // conversion recoverably instead ([temp.inst]/17: a failed
      // required instantiation is diagnosed, not fatal to the tool).
      error().source_location = expr.source_location();
      error() << "constructor '" << expr.function().get(ID_identifier)
              << "' is not a member of its class (partial elaboration?)" << eom;
      throw 0;
    }

    // special case for the initialization of parents
    if(member.get_bool(ID_C_not_accessible))
    {
      PRECONDITION(!member.get(ID_C_access).empty());
      tmp_object_expr.set(ID_C_not_accessible, true);
      tmp_object_expr.set(ID_C_access, member.get(ID_C_access));
    }

    // the constructor is being used, so make sure the destructor
    // will be available
    {
      // find name of destructor
      const struct_union_typet::componentst &components =
        (tmp_object_expr.type().id() == ID_union_tag
           ? static_cast<const struct_union_typet &>(
               follow_tag(to_union_tag_type(tmp_object_expr.type())))
           : static_cast<const struct_union_typet &>(
               follow_tag(to_struct_tag_type(tmp_object_expr.type()))))
          .components();

      for(const auto &c : components)
      {
        const typet &type = c.type();

        if(
          !c.get_bool(ID_from_base) && type.id() == ID_code &&
          to_code_type(type).return_type().id() == ID_destructor)
        {
          add_method_body(&symbol_table.get_writeable_ref(c.get_name()));
          break;
        }
      }
    }

    expr.function().swap(member);

    // `T()' / `T{}': no argument before the implicit object argument is
    // added below -- value-initialization ([expr.type.conv]/2,
    // [dcl.init.general]/16.4).  Not for the constructor call
    // cpp_constructor synthesizes to initialize an object: there the
    // caller distinguishes default- from value-initialization.
    const bool value_initialization =
      expr.arguments().empty() && !expr.get_bool(ID_C_default_initialization);

    typecheck_method_application(expr);
    typecheck_function_call_arguments(expr);

    // N5008 [class.inhctor.init]/1: if the call NAMED class D but the
    // selected constructor is an INHERITED one (its own class B is a
    // base of D, imported by `using B::B;`), the constructor initializes
    // the B base subobject of a D object -- the temporary must be typed
    // D, with the base constructor applied through a derived-to-base
    // pointer conversion ([conv.ptr]/3).  Without this, the temporary
    // was typed B and the enclosing context's conversion to D failed
    // ("invalid implicit conversion from 'struct pf' to 'struct bb'",
    // the libc++ __bind_back_t shape, whose function-template caller was
    // then silently dropped).
    if(orig_function_name.is_not_nil())
    {
      exprt type_probe;
      try
      {
        cpp_typecheck_fargst no_fargs;
        cpp_save_scopet probe_scope(cpp_scopes);
        type_probe = resolve(
          to_cpp_name(orig_function_name),
          cpp_typecheck_resolvet::wantt::TYPE,
          no_fargs,
          /*fail_with_exception=*/false);
      }
      catch(...)
      {
        type_probe.make_nil();
      }
      if(
        type_probe.id() == ID_type && type_probe.type().id() == ID_struct_tag &&
        tmp_object_expr.type().id() == ID_struct_tag)
      {
        const irep_idt d_tag =
          to_struct_tag_type(type_probe.type()).get_identifier();
        const irep_idt b_tag =
          to_struct_tag_type(tmp_object_expr.type()).get_identifier();
        if(d_tag != b_tag)
        {
          const struct_typet &d_struct =
            follow_tag(to_struct_tag_type(type_probe.type()));
          bool b_is_base = false;
          for(const auto &base : d_struct.bases())
          {
            if(to_struct_tag_type(base.type()).get_identifier() == b_tag)
              b_is_base = true;
          }
          // Only the TEMPLATE-inheritance path needs this: a base
          // constructor TEMPLATE is made visible in D via a scope alias
          // (not as a component of D), so resolution materializes a
          // B-typed temporary.  Non-template inherited constructors are
          // imported as D COMPONENTS and are already handled by the
          // member machinery -- re-patching them double-adjusts `this`
          // and aborts.  Distinguish by whether the selected
          // constructor's symbol is among D's components.
          bool ctor_is_d_component = false;
          if(b_is_base)
          {
            const irep_idt ctor_id = expr.function().get(ID_component_name);
            for(const auto &c : d_struct.components())
            {
              if(c.get_name() == ctor_id)
              {
                ctor_is_d_component = true;
                break;
              }
            }
          }
          if(
            b_is_base && !ctor_is_d_component &&
            d_struct.get_bool("has_inherited_constructor"))
          {
            // retype the temporary as D and route the constructor's
            // `this` through a derived-to-base conversion
            const typet b_ptr = pointer_type(tmp_object_expr.type());
            tmp_object_expr.type() = type_probe.type();
            exprt::operandst &args = expr.arguments();
            if(!args.empty() && args.front().id() == ID_address_of)
            {
              exprt &obj = to_address_of_expr(args.front()).object();
              if(obj.id() == ID_new_object)
              {
                obj.type() = type_probe.type();
                args.front().type() = pointer_type(type_probe.type());
                args.front() = typecast_exprt(args.front(), b_ptr);
              }
            }
          }
        }
      }
    }

    const code_expressiont new_code(expr);
    // N5008 [dcl.init.general]/9.1: value-initialization of a class whose
    // default constructor is not user-provided (implicitly declared or
    // defaulted on its first declaration) zero-initializes the object
    // before the constructor runs; cpp_constructor / new_temporary do the
    // same for the functional-cast form that is not resolved through a
    // constructor symbol.  Previously `T()' left such members
    // indeterminate.
    if(
      value_initialization &&
      value_initialization_zero_initializes(tmp_object_expr.type()))
    {
      const auto zero = itanium_abi_cpp_zero_initializer(
        tmp_object_expr.type(), expr.source_location(), *this);
      if(zero.has_value())
      {
        exprt zero_target(ID_new_object, tmp_object_expr.type());
        zero_target.set(ID_C_lvalue, true);
        code_blockt value_init;
        value_init.add(code_expressiont{side_effect_expr_assignt{
          std::move(zero_target),
          zero.value(),
          tmp_object_expr.type(),
          expr.source_location()}});
        value_init.add(new_code);
        tmp_object_expr.add(ID_initializer) = value_init;
        expr.swap(tmp_object_expr);
        return;
      }
    }
    tmp_object_expr.add(ID_initializer) = new_code;
    expr.swap(tmp_object_expr);
    return;
  }

  PRECONDITION(expr.operands().size() == 2);

  if(expr.function().id() == ID_member)
  {
    typecheck_method_application(expr);
    // Update return type after method application — the method's auto
    // return type may have been deduced during convert_function.
    if(has_auto(expr.type()))
      expr.type() = to_code_type(expr.function().type()).return_type();
  }
  else
  {
    // N5008 [dcl.spec.auto.general]/11-13: a call to a function with a
    // placeholder return type needs the type deduced from the function's
    // definition here.  A namespace-scope function's definition is converted
    // eagerly for that reason (cpp_declarator_converter), a non-static
    // member's when called through the member syntax
    // (typecheck_method_application); a STATIC member function template
    // specialization named directly (`_S_convert(source)' in
    // std::filesystem::path's constructor template) reached this point
    // with the placeholder still in its type, and its result could not
    // initialize anything ("found no match for symbol 'str'").
    if(
      expr.function().id() == ID_symbol &&
      expr.function().type().id() == ID_code &&
      has_auto(to_code_type(expr.function().type()).return_type()))
    {
      symbolt *callee_symbol = symbol_table.get_writeable(
        to_symbol_expr(expr.function()).get_identifier());
      // a deferred member (see add_method_body) converts under its own map
      if(
        callee_symbol != nullptr &&
        deferred_method_bodies.count(callee_symbol->name) != 0 &&
        convert_deferred_method_now(callee_symbol->name))
      {
        expr.function().type() = callee_symbol->type;
      }
      if(
        callee_symbol != nullptr && callee_symbol->value.is_not_nil() &&
        callee_symbol->value.id() != ID_cpp_not_typechecked &&
        callee_symbol->value.type().id() != ID_code &&
        functions_being_typechecked.count(callee_symbol->name) == 0)
      {
        cpp_saved_template_mapt saved_map(template_map);
        prepare_deferred_method_body(*callee_symbol);
        try
        {
          convert_function(*callee_symbol);
        }
        catch(...)
        {
          // the body's conversion reports its own failure; the call keeps
          // the placeholder type
        }
        deferred_typechecking.erase(callee_symbol->name);
        for(auto it = method_bodies.begin(); it != method_bodies.end(); ++it)
        {
          if(
            it->method_symbol != nullptr &&
            it->method_symbol->name == callee_symbol->name)
          {
            method_bodies.erase(it);
            break;
          }
        }
        expr.function().type() = callee_symbol->type;
        expr.type() = to_code_type(callee_symbol->type).return_type();
      }
    }

    // for the object of a method call,
    // we are willing to add an "address_of"
    // for the sake of operator overloading

    const code_typet::parameterst &parameters =
      to_code_type(expr.function().type()).parameters();

    if(
      !parameters.empty() && parameters.front().get_this() &&
      !expr.arguments().empty())
    {
      const code_typet::parametert &parameter = parameters.front();

      exprt &operand = expr.arguments().front();
      INVARIANT(
        parameter.type().id() == ID_pointer,
        "`this' parameter should be a pointer");

      if(
        operand.type().id() != ID_pointer &&
        operand.type() == to_pointer_type(parameter.type()).base_type())
      {
        address_of_exprt tmp(operand, pointer_type(operand.type()));
        tmp.add_source_location() = operand.source_location();
        operand = tmp;
      }
    }
  }

  CHECK_RETURN(expr.operands().size() == 2);

  // Generic lambda instantiation: if the call target is a generic lambda,
  // instantiate a new version with the actual argument types.
  instantiate_generic_lambda(expr);

  typecheck_function_call_arguments(expr);

  CHECK_RETURN(expr.operands().size() == 2);

  add_implicit_dereference(expr);

  // Trigger elaboration of lazily deferred template method bodies.
  // A member call's callee is a member_exprt whose component names the
  // method symbol ([temp.inst]/4: odr-use requires implicit
  // instantiation) -- e.g. std::string::rfind, whose out-of-line .tcc
  // body reached the extern-instantiated basic_string<char> only
  // through the deferred queue.
  if(expr.function().id() == ID_member && unevaluated_operand_depth == 0)
  {
    const irep_idt &component = expr.function().get(ID_component_name);
    auto it = deferred_method_bodies.find(component);
    if(it != deferred_method_bodies.end())
    {
      method_bodies.push_back(std::move(it->second));
      deferred_method_bodies.erase(it);
    }
  }
  const auto sym_expr = expr_try_dynamic_cast<symbol_exprt>(expr.function());
  if(sym_expr != nullptr && unevaluated_operand_depth == 0)
  {
    auto it = deferred_method_bodies.find(sym_expr->get_identifier());
    if(it != deferred_method_bodies.end())
    {
      method_bodies.push_back(std::move(it->second));
      deferred_method_bodies.erase(it);
    }
  }

  // constexpr function evaluation
  if(auto sym_expr = expr_try_dynamic_cast<symbol_exprt>(expr.function()))
  {
    const auto *symbol_ptr = symbol_table.lookup(sym_expr->get_identifier());
    // The body is recognised as code either by `value.type().id() ==
    // ID_code` (post-`convert_function`, when the body's TYPE is set
    // to the function's code type) or by `value.id() == ID_code`
    // (the parsed/queued state where the value IS a code block but
    // its type field is empty).  Accept both — the second case
    // matters when we are about to eagerly convert the body so it
    // gets resolved in its own (class) scope.
    bool body_is_code =
      symbol_ptr != nullptr && (symbol_ptr->value.type().id() == ID_code ||
                                symbol_ptr->value.id() == ID_code);
    bool eligible_constexpr =
      symbol_ptr != nullptr && symbol_ptr->is_macro &&
      constant_expression_context != 0 &&
      !functions_being_typechecked.count(sym_expr->get_identifier()) &&
      !deferred_typechecking.count(sym_expr->get_identifier()) && body_is_code;
    if(eligible_constexpr)
    {
      // Pre-check whether the arguments are fully constant: if not,
      // there is no way constexpr-eval can fold the call regardless
      // of whether the body is resolved.  Skipping the eager-convert
      // path in that case avoids unnecessary cascading instantiations
      // for runtime-only invocations of constexpr methods.
      bool args_are_constant_pre = true;
      for(const auto &arg : expr.arguments())
      {
        if(!is_constexpr_call_argument(arg, symbol_table))
        {
          args_are_constant_pre = false;
          break;
        }
      }
      // For constexpr methods of a template class whose body was
      // queued by `add_method_body` but not yet processed, the body's
      // expressions are still in cpp_name form.  Substituting and
      // installing such a body at the call site would leave
      // unresolved names in the caller's scope.  Eagerly process the
      // body via convert_function so it is type-checked in the
      // function's own (class) scope first.  We restrict this to
      // class methods (have a `C_member_name`) where the body has
      // not yet been type-checked (its type field is still empty)
      // and where the body actually contains unresolved cpp_names.
      // The cpp_name guard avoids unwanted cascading instantiations
      // for already-resolved methods that just happen to lack a code
      // type on their `value`.
      bool needs_eager_convert = false;
      // N5008 [temp.inst]/5, [expr.const]: a NON-member constexpr function
      // (template specialization) whose definition still sits in the deferred
      // queue -- first referenced by a run-time call, now needed as a constant
      // (`constexpr auto c = wrap<double>()` after `wrap<double>()` in a
      // plain expression) -- is converted under the queue entry's recorded
      // template map.  Folding the PARSED body here instead substituted
      // `inner<T>()` into the caller's scope, where `T` is unbound ("found no
      // match for symbol 'inner'").
      if(
        args_are_constant_pre &&
        symbol_ptr->type.get(ID_C_member_name).empty() &&
        symbol_ptr->value.type().id() != ID_code &&
        convert_deferred_method_now(sym_expr->get_identifier()))
      {
        symbol_ptr = symbol_table.lookup(sym_expr->get_identifier());
        eligible_constexpr =
          symbol_ptr != nullptr && symbol_ptr->value.type().id() == ID_code;
      }
      else if(
        args_are_constant_pre &&
        !symbol_ptr->type.get(ID_C_member_name).empty() &&
        symbol_ptr->value.type().id() != ID_code)
      {
        // Walk the body's full irept tree (operands AND types and
        // other named-sub fields).  exprt::visit_pre only walks
        // operands, so a `cpp_name` appearing as the `type` field
        // of an inner expression (e.g., the target type of a
        // `static_cast<int_type>(...)`) is invisible to it.  Such
        // cpp_names must still trigger eager-convert: when the
        // body is later substituted into the caller's scope by
        // the constexpr inliner, an unresolved `int_type`
        // cpp_name in the substituted expression's type field
        // surfaces as the spurious diagnostic
        //
        //   invalid implicit conversion from '<<type:cpp_name>>'
        //   to 'signed int'
        //
        // even though `int_type` is a perfectly resolvable
        // typedef in the function's own (class) scope.  Walk the
        // full irept tree to detect any unresolved cpp_name
        // anywhere in the body.
        //
        // Likewise an expression node WITHOUT a type: the parsed body's
        // operators (`__INT_MAX__ * 2U + 1', libstdc++'s
        // numeric_limits<unsigned>::max, in an explicit specialization
        // whose members are queued) carry no type until type-checked, and
        // substituting them made the caller's `>' fail with "conversion
        // from '<<type:>>' ... not permitted".
        std::function<void(const irept &)> needs_typecheck = [&](const irept &n)
        {
          if(needs_eager_convert)
            return;
          if(n.id() == ID_cpp_name)
          {
            needs_eager_convert = true;
            return;
          }
          if(
            (n.id() == ID_plus || n.id() == ID_minus || n.id() == ID_mult ||
             n.id() == ID_div || n.id() == ID_mod || n.id() == ID_shl ||
             n.id() == ID_shr || n.id() == ID_bitand || n.id() == ID_bitor ||
             n.id() == ID_bitxor || n.id() == ID_unary_minus ||
             n.id() == ID_bitnot || n.id() == ID_typecast || n.id() == ID_if) &&
            n.find(ID_type).is_nil())
          {
            needs_eager_convert = true;
            return;
          }
          for(const auto &s : n.get_sub())
            needs_typecheck(s);
          for(const auto &ns : n.get_named_sub())
            needs_typecheck(ns.second);
        };
        needs_typecheck(symbol_ptr->value);
      }
      if(needs_eager_convert)
      {
        symbolt &writeable =
          symbol_table.get_writeable_ref(sym_expr->get_identifier());
        const irep_idt class_id = writeable.type.get(ID_C_member_name);
        const symbolt *class_sym = symbol_table.lookup(class_id);
        cpp_saved_template_mapt saved_map(template_map);
        if(
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template).is_not_nil() &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil())
        {
          template_map.build(
            static_cast<const template_typet &>(
              class_sym->type.find(ID_C_template)),
            static_cast<const cpp_template_args_tct &>(
              class_sym->type.find(ID_C_template_arguments)));
        }
        methods_seen.insert(sym_expr->get_identifier());
        // N5008 [temp.inst]/1: an instantiated member function TEMPLATE
        // additionally needs its own template map (the #fn_template_*
        // records) on top of the class map built above -- without it a
        // body like `__is_constructible(T2, U2)` leaves U2 unresolved
        // and the conversion fails, so a requires-clause call atom
        // (pair's _S_constructible<_U1,_U2>()) never folds.
        prepare_deferred_method_body(writeable);
        try
        {
          convert_function(writeable);
        }
        catch(...)
        {
          // typecheck failure: leave value unchanged, fall through to
          // the symbol_ptr->value check below which will see whatever
          // state the body is in
        }
        symbol_ptr = symbol_table.lookup(sym_expr->get_identifier());
        eligible_constexpr =
          symbol_ptr != nullptr && symbol_ptr->value.type().id() == ID_code;
      }
    }
    if(eligible_constexpr)
    {
      // N5008 [expr.const]/5 + [temp.inst]/5: evaluate the call with the
      // interpreting constant evaluator (try_evaluate_constexpr), which runs
      // the constexpr function's statements -- declarations, loops,
      // assignments, nested calls -- on constant arguments.  A callee whose
      // definition still sits in the deferred method-body queue is converted
      // on demand under its recorded template map (the callback), exactly as
      // the call site above did for the outermost callee.  When the
      // evaluation cannot produce a constant the call stays a run-time
      // invocation (is_macro is deliberately kept: the same function may be
      // evaluable with other, constant, arguments later).
      exprt r = try_evaluate_constexpr(
        expr,
        symbol_table,
        *this,
        [this](const irep_idt &callee) -> bool
        {
          const symbolt *csym = symbol_table.lookup(callee);
          if(csym == nullptr || !csym->is_macro)
            return false;
          if(csym->value.type().id() == ID_code)
            return true; // already converted
          if(
            functions_being_typechecked.count(callee) != 0 ||
            deferred_typechecking.count(callee) != 0)
          {
            return false;
          }
          return convert_deferred_method_now(callee);
        });
      if(r.is_not_nil())
      {
        r.add_source_location() = expr.source_location();
        expr.swap(r);
        return;
      }
    }
  }

  // we will deal with some 'special' functions here
  //
  // do_special_functions (shared with the C front-end) recognises built-ins
  // such as __builtin_*_overflow and the __CPROVER_* intrinsics by matching the
  // function operand's identifier against plain names like
  // "__builtin_mul_overflow".  In C++ the resolved function symbol's identifier
  // additionally carries a parameter-signature suffix (e.g.
  // "__builtin_mul_overflow()"), so those matches would never fire.  Try the
  // shared handling on a copy whose function operand has been renamed to its
  // base name, so that everything do_special_functions supports is also
  // available in C++.  These built-ins are GCC/Clang extensions, not specified
  // by N5008; their semantics follow the GCC documentation as implemented by
  // do_special_functions.
  exprt tmp = nil_exprt();
  if(expr.function().id() == ID_symbol)
  {
    const irep_idt &fid = to_symbol_expr(expr.function()).get_identifier();
    const symbolt *fsym = symbol_table.lookup(fid);
    if(fsym != nullptr && fsym->base_name != fid)
    {
      side_effect_expr_function_callt normalized = expr;
      to_symbol_expr(normalized.function()).set_identifier(fsym->base_name);
      tmp = do_special_functions(normalized);
    }
  }
  if(tmp.is_nil())
    tmp = do_special_functions(expr);
  if(tmp.is_not_nil())
    expr.swap(tmp);
} // NOLINT(readability/fn_size)

/// \param expr: function call whose arguments need to be checked
/// N5008 [class.mem.general]/7-8, [dcl.fct.default]: a default argument
/// declared in a class member-specification is a complete-class context.
/// typecheck_type kept it unchecked (wrapped with the declaring scope); this
/// checks it in that scope -- with the class's template parameters bound
/// when the class is a template specialization ([temp.inst]/4 names in the
/// default argument refer to the specialization's arguments) -- and converts
/// it to the parameter type ([dcl.init]).
exprt cpp_typecheckt::typecheck_deferred_default_argument(const exprt &deferred)
{
  PRECONDITION(deferred.id() == ID_cpp_deferred_default_argument);
  PRECONDITION(deferred.operands().size() == 1);

  exprt value = to_unary_expr(deferred).op();
  const irep_idt scope_id = deferred.get(ID_C_identifier);

  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_saved_template_mapt saved_map(template_map);

  const auto scope_it = cpp_scopes.id_map.find(scope_id);
  if(scope_it != cpp_scopes.id_map.end() && scope_it->second->is_scope)
  {
    cpp_scopes.set_scope(scope_id);
    // the class scope of a specialization: its identifier is the class
    // symbol's name
    const symbolt *class_symbol = symbol_table.lookup(scope_id);
    if(
      class_symbol != nullptr && class_symbol->is_type &&
      class_symbol->type.find(ID_C_template_arguments).is_not_nil())
    {
      bind_class_instance_parameters(*class_symbol, template_map);
    }
  }

  typecheck_expr(value);
  implicit_typecast(value, deferred.type());
  return value;
}

void cpp_typecheckt::typecheck_function_call_arguments(
  side_effect_expr_function_callt &expr)
{
  exprt &f_op = expr.function();
  const code_typet &code_type = to_code_type(f_op.type());
  const code_typet::parameterst &parameters = code_type.parameters();

  // N5008 [expr.call]/7: when a function is called, the type of a parameter
  // shall not be an incomplete class type (a parameter passed by value);
  // the call requires the class to be complete ([temp.inst]/2).  In a
  // requirement this makes the requirement unsatisfied
  // ([expr.prim.req.general]/5): `requires(I a, I b) { a - b; }' with I an
  // incomplete wrapper<incomplete>.
  for(const auto &parameter : parameters)
  {
    const typet &parameter_type = parameter.type();
    if(parameter_type.id() != ID_struct_tag || parameter.get_this())
      continue;
    elaborate_class_template(parameter_type);
    const symbolt *class_symbol =
      symbol_table.lookup(to_struct_tag_type(parameter_type).get_identifier());
    if(
      class_symbol != nullptr && class_symbol->type.id() == ID_struct &&
      to_struct_type(class_symbol->type).is_incomplete())
    {
      error().source_location = expr.source_location();
      error() << "call of '" << to_string(f_op)
              << "' with a parameter of incomplete type '"
              << to_string(parameter_type) << "'" << eom;
      throw 0;
    }
  }

  // do default arguments

  if(parameters.size() > expr.arguments().size())
  {
    std::size_t i = expr.arguments().size();

    for(; i < parameters.size(); i++)
    {
      if(!parameters[i].has_default_value())
        break;

      exprt value = parameters[i].default_value();
      if(value.id() == ID_cpp_deferred_default_argument)
        value = typecheck_deferred_default_argument(value);
      expr.arguments().push_back(std::move(value));
    }
  }

  exprt::operandst::iterator arg_it = expr.arguments().begin();
  for(const auto &parameter : parameters)
  {
    // Stop once the supplied arguments are exhausted.  A well-formed call has
    // at least as many arguments as non-defaulted parameters (defaults were
    // filled in above), but an ill-formed call synthesized during template
    // instantiation -- e.g. a variadic pack-expansion use that was expanded to
    // too few arguments -- can leave fewer arguments than parameters here.
    // Dereferencing `arg_it` past `end()` is undefined behaviour (it corrupted
    // the shared-irep tree and crashed); break instead and let the arity
    // mismatch be diagnosed by the base type-checker below.
    if(arg_it == expr.arguments().end())
      break;

    if(parameter.get_bool(ID_C_call_by_value))
    {
      DATA_INVARIANT(is_reference(parameter.type()), "reference expected");

      if(arg_it->id() != ID_temporary_object)
      {
        // create a temporary for the parameter

        exprt temporary;
        new_temporary(
          arg_it->source_location(),
          to_reference_type(parameter.type()).base_type(),
          already_typechecked_exprt{*arg_it},
          temporary);
        arg_it->swap(temporary);
      }
    }
    else if(
      is_rvalue_reference(parameter.type()) &&
      arg_it->type().id() != ID_pointer && arg_it->id() != ID_address_of &&
      arg_it->id() != ID_temporary_object && arg_it->id() != ID_dereference &&
      (arg_it->type().id() == ID_struct_tag ||
       arg_it->type().id() == ID_struct ||
       arg_it->type().id() == ID_union_tag || arg_it->type().id() == ID_union))
    {
      // [dcl.init.ref] p5: An rvalue reference binds to an rvalue.
      // When the argument is a struct/union value (including function
      // call results), take its address to create the reference binding.
      // For side_effect (function call) results, the result is
      // materialized as a temporary by the GOTO conversion.
      //
      // A struct-literal PRVALUE (a struct_exprt, e.g. libc++'s
      // `__default_init_tag()` passed to __compressed_pair's
      // forwarding-reference constructor) has no storage to point at:
      // [class.temporary]/3, [dcl.init.ref]/5.4 require materializing
      // a temporary first.  A raw address-of over the literal reached
      // symbolic execution and aborted address_arithmetic.
      if(arg_it->id() == ID_struct)
      {
        // Wrap the literal in a temporary-object side effect (the
        // GOTO conversion materializes it into addressable storage);
        // routing through new_temporary/cpp_constructor here would
        // re-enter overload resolution mid-argument-conversion.
        side_effect_exprt tmp_object_expr(
          ID_temporary_object, arg_it->type(), arg_it->source_location());
        tmp_object_expr.copy_to_operands(*arg_it);
        tmp_object_expr.set(ID_C_lvalue, true);
        tmp_object_expr.set(ID_mode, ID_cpp);
        exprt addr = address_of_exprt(tmp_object_expr);
        addr.type() = parameter.type();
        arg_it->swap(addr);
      }
      else
      {
        exprt addr = address_of_exprt(*arg_it);
        const typet &ref_base = to_reference_type(parameter.type()).base_type();
        if(
          arg_it->type().id() == ID_struct_tag &&
          ref_base.id() == ID_struct_tag &&
          to_struct_tag_type(arg_it->type()).get_identifier() !=
            to_struct_tag_type(ref_base).get_identifier())
        {
          // N5008 [dcl.init.ref]/5.3.1: `Base &&' bound to a Derived
          // prvalue -- the reference is to the BASE subobject: a
          // derived-to-base pointer adjustment, not a retyped address
          // (symex rejected the mistyped address_of).
          make_ptr_typecast(addr, to_reference_type(parameter.type()));
          addr.type() = parameter.type();
        }
        else
          addr.type() = parameter.type();
        arg_it->swap(addr);
      }
    }
    else if(
      parameter.type().id() == ID_struct_tag &&
      arg_it->id() != ID_temporary_object && arg_it->id() != ID_side_effect)
    {
      // Brace-init-list to std::initializer_list<T>: convert before
      // the copy-constructor path so that new_temporary sees a struct,
      // not a raw brace-init-list.
      if(
        arg_it->id() == ID_initializer_list &&
        parameter.type().id() == ID_struct_tag &&
        id2string(to_struct_tag_type(parameter.type()).get_identifier())
            .find("tag-initializer_list<") != std::string::npos)
      {
        implicit_typecast(*arg_it, parameter.type());
        ++arg_it;
        continue;
      }

      // N5008 [over.match.copy] + [over.best.ics]/4: copy-initializing
      // a by-value parameter from a DIFFERENT class is a TWO-STEP
      // process -- first convert the argument to the parameter's class
      // (candidates: the class's converting constructors AND the
      // argument's conversion functions), then initialize from that
      // rvalue.  Resolving the parameter class's constructors directly
      // against the raw argument instead runs direct-initialization,
      // where a `template <class C> operator C()` on the argument makes
      // EVERY constructor viable via a user-defined conversion of its
      // first parameter (forbidden by [over.best.ics]/4), reporting a
      // bogus ambiguity across all of std::vector's constructors.
      // Derived-to-base by-value (slicing) stays on the constructor
      // path: binding derived to `const base &` is a standard
      // conversion, not a user-defined one.
      if(
        arg_it->type().id() == ID_struct_tag &&
        arg_it->type() != parameter.type() &&
        !subtype_typecast(
          follow_tag(to_struct_tag_type(arg_it->type())),
          follow_tag(to_struct_tag_type(parameter.type()))))
      {
        implicit_typecast(*arg_it, parameter.type());
        ++arg_it;
        continue;
      }

      // Non-POD class-type pass-by-value: call copy constructor.
      // Check that the destructor symbol exists (needed for the
      // temporary) to avoid crashes during goto conversion.
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(parameter.type()));
      bool has_dtor = false;
      for(const auto &c : struct_type.components())
      {
        if(
          c.type().id() == ID_code &&
          to_code_type(c.type()).return_type().id() == ID_destructor)
        {
          const symbolt *dtor_sym;
          has_dtor = !lookup(c.get_name(), dtor_sym);
          break;
        }
      }
      if(has_dtor)
      {
        exprt temporary;
        if(
          arg_it->id() == ID_initializer_list &&
          !has_viable_init_list_constructor(parameter.type(), *arg_it))
        {
          // N5008 [over.match.list]/1: list-initializing the by-value
          // parameter's temporary considers initializer-list
          // constructors with the list as a single argument only in
          // phase 1; otherwise the ELEMENTS are the constructor
          // arguments (phase 2).  Passing the raw list as one argument
          // made overload resolution pick the copy constructor and
          // then fail converting the first element to the class's
          // reference ([over.best.ics.general]/4 forbids that user
          // conversion for constructor candidates): `take({2, a})`
          // with itemt(int, const valt&) mispaired 2 -> const valt&.
          exprt::operandst element_ops;
          element_ops.reserve(arg_it->operands().size());
          for(auto &element : arg_it->operands())
          {
            typecheck_expr(element);
            element_ops.push_back(already_typechecked_exprt{element});
          }
          new_temporary(
            arg_it->source_location(),
            parameter.type(),
            element_ops,
            temporary);
        }
        else
        {
          new_temporary(
            arg_it->source_location(),
            parameter.type(),
            already_typechecked_exprt{*arg_it},
            temporary);
        }
        arg_it->swap(temporary);
      }
    }

    ++arg_it;
  }

  c_typecheck_baset::typecheck_function_call_arguments(expr);
}

/// Replace `auto` (or `cpp_name`) in a type tree with the given replacement.
/// Handles `const auto &`, `auto *`, etc.
static void replace_auto_in_type(typet &type, const typet &replacement)
{
  if(type.id() == ID_auto || type.id() == ID_cpp_name)
  {
    type = replacement;
    return;
  }

  if(
    type.id() == ID_merged_type || type.id() == ID_frontend_pointer ||
    type.id() == ID_pointer)
  {
    for(auto &sub : to_type_with_subtypes(type).subtypes())
      replace_auto_in_type(sub, replacement);
  }
}

void cpp_typecheckt::instantiate_generic_lambda(
  side_effect_expr_function_callt &expr)
{
  // Resolve the lambda function name from the call target.
  // The function expression is either:
  //   dereference(symbol("var")) — indirect call through variable
  //   symbol("lambda_func") — direct call
  irep_idt lambda_name;

  if(expr.function().id() == ID_dereference)
  {
    const exprt &inner = to_dereference_expr(expr.function()).pointer();
    if(inner.id() == ID_symbol)
    {
      const symbolt &var_sym =
        symbol_table.lookup_ref(to_symbol_expr(inner).get_identifier());
      // The variable's value should be address_of(symbol(lambda_func))
      if(
        var_sym.value.id() == ID_address_of &&
        to_address_of_expr(var_sym.value).object().id() == ID_symbol)
      {
        lambda_name = to_symbol_expr(to_address_of_expr(var_sym.value).object())
                        .get_identifier();
      }
    }
  }
  else if(expr.function().id() == ID_symbol)
  {
    lambda_name = to_symbol_expr(expr.function()).get_identifier();
  }

  if(lambda_name.empty())
    return;

  auto it = generic_lambda_map.find(lambda_name);
  if(it == generic_lambda_map.end())
    return;

  // Build the list of actual argument types
  std::vector<typet> arg_types;
  for(auto &arg : expr.arguments())
  {
    if(arg.type().is_nil() || arg.type().id().empty())
      typecheck_expr(arg);
    arg_types.push_back(arg.type());
  }

  // Build a mangled name for this instantiation
  std::string inst_name = id2string(lambda_name);
  for(const auto &t : arg_types)
    inst_name += "#" + cpp_type2name(t);

  // Check if we already instantiated this specialization
  if(symbol_table.has_symbol(inst_name))
  {
    // Redirect the call to the existing instantiation
    const symbolt &inst_sym = symbol_table.lookup_ref(inst_name);
    const code_typet &inst_type = to_code_type(inst_sym.type);
    if(expr.function().id() == ID_dereference)
    {
      expr.function() = symbol_exprt(inst_name, inst_type);
      expr.type() = inst_type.return_type();
    }
    return;
  }

  // Create a fresh copy of the original lambda expression
  exprt lambda_expr = it->second;

  // Replace auto/template parameters with actual argument types.
  // Build a mapping from template parameter names to actual types
  // (for C++20 template lambdas where params use named types like T).
  std::map<irep_idt, typet> type_map;
  irept &params = lambda_expr.add(ID_parameters);
  std::size_t arg_idx = 0;
  for(auto &p : params.get_sub())
  {
    cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
    if(pdecl.get_bool("explicit_this"))
      continue;
    if(arg_idx < arg_types.size())
    {
      if(has_auto(pdecl.type()) || pdecl.type().id() == ID_auto)
      {
        replace_auto_in_type(pdecl.type(), arg_types[arg_idx]);
      }
      else if(pdecl.type().id() == ID_cpp_name)
      {
        // Template lambda: map the type name to the actual type
        irep_idt tname = pdecl.type().get_sub().front().get(ID_identifier);
        type_map[tname] = arg_types[arg_idx];
        pdecl.type() = arg_types[arg_idx];
      }
    }
    arg_idx++;
  }

  // Replace template type names in the return type
  {
    irept &ret_type = lambda_expr.add(ID_return_type);
    if(ret_type.is_not_nil() && ret_type.id() == ID_cpp_name)
    {
      irep_idt rname = ret_type.get_sub().front().get(ID_identifier);
      auto tm = type_map.find(rname);
      if(tm != type_map.end())
        ret_type = static_cast<const irept &>(tm->second);
    }
  }

  // Now type-check this lambda as a non-generic lambda with the inst_name
  // We do this by calling typecheck_expr_lambda with the modified expression.
  // But since typecheck_expr_lambda uses a counter for naming, we need to
  // set up the name manually.

  // Extract the scope prefix from the original lambda name
  // e.g., "main::1::__lambda_0" -> scope prefix is "main::1::"
  std::string orig = id2string(lambda_name);
  auto last_sep = orig.rfind("::");
  std::string scope_prefix =
    (last_sep != std::string::npos) ? orig.substr(0, last_sep + 2) : "";

  // Use inst_name as the function symbol name
  const source_locationt &loc = lambda_expr.source_location();

  // Collect parameters
  code_typet::parameterst func_params;
  for(const auto &p : params.get_sub())
  {
    const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
    if(pdecl.get_bool("explicit_this"))
      continue;
    typet ptype = pdecl.type();
    if(!ptype.id().empty())
      typecheck_type(ptype);
    irep_idt pname;
    if(!pdecl.declarators().empty())
      pname =
        pdecl.declarators().front().name().get_sub().front().get(ID_identifier);
    code_typet::parametert param(ptype);
    param.set_identifier(inst_name + "::" + id2string(pname));
    param.set_base_name(pname);
    func_params.push_back(param);
  }

  // Create parameter symbols
  for(const auto &p : func_params)
  {
    if(symbol_table.has_symbol(p.get_identifier()))
      continue;
    auxiliary_symbolt psym;
    psym.name = p.get_identifier();
    psym.base_name = p.get_base_name();
    psym.type = p.type();
    psym.mode = ID_cpp;
    psym.module = module;
    psym.location = loc;
    psym.is_file_local = true;
    psym.is_thread_local = true;
    psym.is_lvalue = true;
    psym.is_parameter = true;
    symbol_table.insert(std::move(psym));
  }

  // Collect captures from the original lambda
  const irept &capture_list = lambda_expr.find("lambda_capture");
  std::map<irep_idt, exprt> capture_values;
  std::set<irep_idt> by_ref_captures;
  for(const auto &cap : capture_list.get_sub())
  {
    irep_idt cap_name = cap.get(ID_identifier);
    if(cap_name.empty())
      continue;
    if(cap.get_bool("by_ref"))
      by_ref_captures.insert(cap_name);
    const exprt &init = static_cast<const exprt &>(cap.find("init"));
    if(init.is_not_nil())
    {
      exprt init_copy = init;
      typecheck_expr(init_copy);
      capture_values[cap_name] = init_copy;
    }
    else
    {
      exprt cap_expr(ID_cpp_name);
      irept name_node(ID_name);
      name_node.set(ID_identifier, cap_name);
      cap_expr.get_sub().push_back(name_node);
      cap_expr.add_source_location() = loc;
      typecheck_expr(cap_expr);
      capture_values[cap_name] = cap_expr;
    }
  }

  // Type-check the body
  typet lambda_return_type = signed_int_type();
  bool deduce_return = true;
  {
    const irept &explicit_ret = lambda_expr.find(ID_return_type);
    if(explicit_ret.is_not_nil() && !explicit_ret.id().empty())
    {
      lambda_return_type = static_cast<const typet &>(explicit_ret);
      // N5008 [dcl.fct]/8: the parameters are in scope in the trailing
      // return type -- `[](int __s) -> decltype(__s)` must resolve
      // `__s` (cvise-reduced from a preprocessed libc++ <string>
      // seed).  Enter the lambda's scope and register the parameters
      // before type-checking the return type, exactly as the body
      // conversion below does.
      cpp_save_scopet save_scope_for_ret(cpp_scopes);
      std::string lambda_base_ret = inst_name.substr(scope_prefix.size());
      cpp_scopet &lambda_scope_ret =
        cpp_scopes.current_scope().new_scope(lambda_base_ret);
      lambda_scope_ret.prefix = inst_name + "::";
      cpp_scopes.go_to(lambda_scope_ret);
      for(const auto &p : func_params)
      {
        const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
        cpp_idt &id = cpp_scopes.put_into_scope(psym);
        id.id_class = cpp_idt::id_classt::SYMBOL;
      }
      typecheck_type(lambda_return_type);
      deduce_return = false;
    }
  }

  code_typet func_type(func_params, lambda_return_type);

  codet body_code(ID_nil);
  {
    cpp_save_scopet save_scope(cpp_scopes);

    // Find or create the lambda scope
    std::string lambda_base = inst_name.substr(scope_prefix.size());
    cpp_scopet &lambda_scope =
      cpp_scopes.current_scope().new_scope(lambda_base);
    lambda_scope.prefix = inst_name + "::";
    cpp_scopes.go_to(lambda_scope);

    for(const auto &p : func_params)
    {
      const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
      cpp_idt &id = cpp_scopes.put_into_scope(psym);
      id.id_class = cpp_idt::id_classt::SYMBOL;
    }

    for(const auto &cap : capture_values)
    {
      if(by_ref_captures.count(cap.first))
      {
        if(cap.second.id() == ID_symbol)
        {
          const symbolt &outer_sym = symbol_table.lookup_ref(
            to_symbol_expr(cap.second).get_identifier());
          // [expr.prim.lambda.capture]/6: `[&r = k]' -- see the non-generic
          // path
          if(outer_sym.base_name != cap.first)
          {
            cpp_idt &cid = cpp_scopes.current_scope().insert(cap.first);
            cid.identifier = outer_sym.name;
            cid.id_class = cpp_idt::id_classt::SYMBOL;
            continue;
          }
          cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
          cid.id_class = cpp_idt::id_classt::SYMBOL;
          continue;
        }
      }

      std::string csym_name = inst_name + "::" + id2string(cap.first);
      if(!symbol_table.has_symbol(csym_name))
      {
        auxiliary_symbolt csym;
        csym.name = csym_name;
        csym.base_name = cap.first;
        csym.type = cap.second.type();
        csym.value = cap.second;
        csym.mode = ID_cpp;
        csym.module = module;
        csym.location = loc;
        csym.is_file_local = true;
        csym.is_thread_local = true;
        csym.is_lvalue = true;
        csym.is_state_var = true;
        symbol_table.insert(std::move(csym));
      }

      const symbolt &inserted = symbol_table.lookup_ref(csym_name);
      cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
      cid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    body_code = to_code(static_cast<exprt &>(lambda_expr.add("body")));

    // Save and restore the enclosing function's return type
    // EXCEPTION-SAFELY (mirroring convert_function's context guard): if
    // type-checking the lambda body throws and an upstream recovery
    // (e.g. a SFINAE guard around a default-argument evaluation) absorbs
    // the exception while the ENCLOSING body continues, a plain
    // assignment-restore would leave `return_type` set to the lambda's
    // -- and the enclosing function's later `return` statements would
    // convert against the wrong type (N5008 [stmt.return]/3 requires
    // conversion to the enclosing function's return type).  No reachable
    // trigger is currently known (corpus probe found none; every valid
    // lambda body tried type-checks), so this is hardening; see
    // regression/cbmc-cpp/cpp11_lambda_return_context.
    return_deduction_contextt return_context{*this, func_type, deduce_return};

    typecheck_code(body_code);

    return_context.finish();

    // (the enclosing return-type context is restored at scope exit)

    // Prepend capture initializations
    if(!capture_values.empty())
    {
      code_blockt block;
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
          continue;
        symbol_exprt cap_sym(
          inst_name + "::" + id2string(cap.first), cap.second.type());
        codet assign(ID_assign);
        assign.copy_to_operands(cap_sym);
        assign.copy_to_operands(cap.second);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }
      if(body_code.get_statement() == ID_block)
      {
        for(auto &stmt : to_code_block(body_code).statements())
          block.add(std::move(stmt));
      }
      else
        block.add(std::move(body_code));
      body_code = std::move(block);
    }
  }

  // Create the function symbol
  symbolt func_sym;
  func_sym.name = inst_name;
  func_sym.base_name = inst_name.substr(scope_prefix.size());
  func_sym.type = func_type;
  func_sym.value = body_code;
  func_sym.mode = ID_cpp;
  func_sym.module = module;
  func_sym.location = loc;
  func_sym.is_file_local = true;
  symbol_table.insert(std::move(func_sym));

  // Redirect the call to the new instantiation
  expr.function() = symbol_exprt(inst_name, func_type);
  expr.type() = func_type.return_type();
}

void cpp_typecheckt::typecheck_expr_side_effect(side_effect_exprt &expr)
{
  const irep_idt &statement = expr.get(ID_statement);

  if(statement == ID_cpp_new || statement == ID_cpp_new_array)
  {
    typecheck_expr_new(expr);
  }
  else if(statement == ID_cpp_delete || statement == ID_cpp_delete_array)
  {
    typecheck_expr_delete(expr);
  }
  else if(
    statement == ID_preincrement || statement == ID_predecrement ||
    statement == ID_postincrement || statement == ID_postdecrement)
  {
    typecheck_side_effect_inc_dec(expr);
  }
  else if(statement == ID_throw)
  {
    typecheck_expr_throw(expr);
  }
  else if(statement == ID_temporary_object)
  {
    // TODO
  }
  else
    c_typecheck_baset::typecheck_expr_side_effect(expr);
}

void cpp_typecheckt::typecheck_method_application(
  side_effect_expr_function_callt &expr)
{
  PRECONDITION(expr.operands().size() == 2);

  PRECONDITION(expr.function().id() == ID_member);
  PRECONDITION(expr.function().operands().size() == 1);

  // turn e.f(...) into xx::f(e, ...)

  exprt member_expr;
  member_expr.swap(expr.function());

  symbolt &method_symbol =
    symbol_table.get_writeable_ref(member_expr.get(ID_component_name));

  const irep_idt &member_name = method_symbol.type.get(ID_C_member_name);

  if(!member_name.empty())
  {
    const symbolt &tag_symbol = lookup(member_name);

    // build the right template map
    // if this is an instantiated template class method
    if(tag_symbol.type.find(ID_C_template) != irept())
    {
      cpp_saved_template_mapt saved_map(template_map);
      const irept &template_type = tag_symbol.type.find(ID_C_template);
      const irept &template_args =
        tag_symbol.type.find(ID_C_template_arguments);
      template_map.build(
        static_cast<const template_typet &>(template_type),
        static_cast<const cpp_template_args_tct &>(template_args));
      add_method_body(&method_symbol);
#ifdef DEBUG
      std::cout << "MAP for " << method_symbol << ":\n";
      template_map.print(std::cout);
#endif
    }
    else
      add_method_body(&method_symbol);
  }
  else
    add_method_body(&method_symbol);

  // N5008 [dcl.spec.auto.general]/15: a member of a class template
  // specialization with a deduced return type is instantiated when used;
  // this call needs its type.  Its body waits in the deferred queue with
  // its template map.
  if(
    method_symbol.type.id() == ID_code &&
    has_auto(to_code_type(method_symbol.type).return_type()) &&
    deferred_method_bodies.count(method_symbol.name) != 0)
  {
    convert_deferred_method_now(method_symbol.name);
  }

  // If the method has an auto return type, force immediate type-checking
  // of the body so the return type is deduced before the call site uses it.
  if(
    method_symbol.type.id() == ID_code &&
    has_auto(to_code_type(method_symbol.type).return_type()) &&
    method_symbol.value.is_not_nil())
  {
    // N5008 [temp.inst]/1: this EAGER conversion of a member function
    // template instance must run under the instance's template map,
    // exactly as the deferred drain does -- the drain's shared
    // preprocessing installs the bindings from #fn_template_type /
    // #fn_template_args and expands replicated parameter packs.
    // Without it the body was converted under the CALLER's map (empty
    // at translation-unit level), the body's use of the method's own
    // template parameter threw ("unbound template parameter"), the
    // auto return type never resolved, and the CALL SITE reported the
    // argument conversion into a raw `auto` (libc++ ranges
    // `arr | std::views::take(3)`: the closure-producing
    // take::operator()(_Np)'s body names _Np()).
    cpp_saved_template_mapt saved_map(template_map);
    prepare_deferred_method_body(method_symbol);
    convert_function(method_symbol);
    // The method-bodies drain warns that convert must never run twice
    // for the same symbol; this EAGER conversion leaves the queued
    // entry behind, and the drain then re-typechecked the
    // already-converted body.  A resolved std::forward call's xvalue
    // result is materialised as a #reference-typed expression, so the
    // re-typecheck rejected re-binding it to the rvalue-reference
    // parameter ("invalid implicit conversion from 'signed int &' to
    // 'signed int &&'" -- N5008 [forward]/4, [dcl.init.ref]/5.3;
    // libc++'s take-closure `auto operator()(_Np&&)` forwarding into
    // __bind_back, the last layer of the range-pipe failure).
    // Remove the queue entry.
    for(auto it = method_bodies.begin(); it != method_bodies.end(); ++it)
    {
      if(
        it->method_symbol != nullptr &&
        it->method_symbol->name == method_symbol.name)
      {
        method_bodies.erase(it);
        break;
      }
    }
  }

  // build new function expression
  exprt new_function(cpp_symbol_expr(method_symbol));
  new_function.add_source_location() = member_expr.source_location();
  expr.function().swap(new_function);

  if(!expr.function().type().get_bool(ID_C_is_static))
  {
    const code_typet &func_type = to_code_type(method_symbol.type);
    typet this_type = func_type.parameters().front().type();

    // C++23 deducing this: first parameter is the object by value,
    // not a pointer.
    if(func_type.get_bool("explicit_this"))
    {
      if(expr.arguments().size() < func_type.parameters().size())
      {
        exprt this_arg = to_member_expr(member_expr).compound();
        implicit_typecast(this_arg, this_type);
        expr.arguments().insert(expr.arguments().begin(), this_arg);
      }
    }
    else
    {
      // Special case. Make it a reference.
      DATA_INVARIANT(this_type.id() == ID_pointer, "this should be pointer");
      this_type.set(ID_C_reference, true);
      this_type.set(ID_C_this, true);

      if(expr.arguments().size() == func_type.parameters().size())
      {
        // this might be set up for base-class initialisation
        if(
          expr.arguments().front().type() !=
          func_type.parameters().front().type())
        {
          implicit_typecast(expr.arguments().front(), this_type);
          DATA_INVARIANT(
            is_reference(expr.arguments().front().type()),
            "argument should be reference");
          expr.arguments().front().type().remove(ID_C_reference);
        }
      }
      else
      {
        exprt this_arg = to_member_expr(member_expr).compound();
        implicit_typecast(this_arg, this_type);
        // For multiple inheritance, the implicit_typecast may produce a
        // simple typecast from derived* to base* without adjusting the
        // pointer offset. Re-do the pointer cast using make_ptr_typecast
        // which handles non-first base class offsets.
        if(
          this_arg.id() == ID_typecast && this_arg.type().id() == ID_pointer &&
          to_typecast_expr(this_arg).op().type().id() == ID_pointer &&
          to_pointer_type(this_arg.type()).base_type().id() == ID_struct_tag &&
          to_pointer_type(to_typecast_expr(this_arg).op().type())
              .base_type()
              .id() == ID_struct_tag)
        {
          // Only adjust for upcasts (derived* -> base*).
          const struct_typet &src_s = follow_tag(to_struct_tag_type(
            to_pointer_type(to_typecast_expr(this_arg).op().type())
              .base_type()));
          const struct_typet &dest_s = follow_tag(
            to_struct_tag_type(to_pointer_type(this_arg.type()).base_type()));
          if(subtype_typecast(src_s, dest_s))
          {
            exprt inner = to_typecast_expr(this_arg).op();
            pointer_typet dest_ptr_type(
              to_pointer_type(this_arg.type()).base_type(),
              to_pointer_type(this_arg.type()).get_width());
            make_ptr_typecast(inner, dest_ptr_type);
            inner.type().set(ID_C_reference, true);
            inner.type().set(ID_C_this, true);
            this_arg = inner;
          }
        }
        DATA_INVARIANT(
          is_reference(this_arg.type()), "argument should be reference");
        this_arg.type().remove(ID_C_reference);
        expr.arguments().insert(expr.arguments().begin(), this_arg);
      }
    } // end else (non-deducing-this)
  }

  if(
    method_symbol.value.id() == ID_cpp_not_typechecked &&
    !method_symbol.value.get_bool(ID_is_used))
  {
    method_symbol.value.set(ID_is_used, true);
  }
}

/// N5008 [expr.assign]/1, [expr.pre.incr]/1: in C++ a built-in assignment,
/// compound assignment or prefix increment/decrement is an lvalue referring
/// to its left operand.  Goto conversion follows C, where the result is the
/// assigned VALUE (held in a temporary when the left operand is not a plain
/// variable, e.g. `*x' for a reference x); it keeps the left operand only when
/// the address of the side effect is taken.  When such a side effect is
/// itself the operand that is modified, `(x += 2) += 3' or `++(++x)', make
/// that explicit as `*&(x += 2)'.
static void use_side_effect_as_lvalue(exprt &operand)
{
  if(operand.id() != ID_side_effect || !operand.get_bool(ID_C_lvalue))
    return;
  const irep_idt &statement = operand.get(ID_statement);
  if(
    statement != ID_assign && statement != ID_assign_plus &&
    statement != ID_assign_minus && statement != ID_assign_mult &&
    statement != ID_assign_div && statement != ID_assign_mod &&
    statement != ID_assign_shl && statement != ID_assign_ashr &&
    statement != ID_assign_lshr && statement != ID_assign_bitand &&
    statement != ID_assign_bitxor && statement != ID_assign_bitor &&
    statement != ID_preincrement && statement != ID_predecrement)
  {
    return;
  }
  const typet type = operand.type();
  const source_locationt location = operand.source_location();
  address_of_exprt address{operand, pointer_type(type)};
  dereference_exprt object{std::move(address), type};
  object.set(ID_C_lvalue, true);
  object.add_source_location() = location;
  operand = std::move(object);
}

void cpp_typecheckt::typecheck_side_effect_assignment(side_effect_exprt &expr)
{
  if(expr.operands().size() == 2)
    use_side_effect_as_lvalue(to_binary_expr(expr).op0());
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.find_source_location();
    error() << "assignment side effect expected to have two operands" << eom;
    throw 0;
  }

  typet type0 = to_binary_expr(expr).op0().type();

  if(is_reference(type0))
    type0 = to_reference_type(type0).base_type();

  const irep_idt statement = expr.get(ID_statement);

  // N5008 [expr.ass]/2-7: there is no built-in compound assignment for class
  // types; `a @= b` on a class type is rewritten to a call to the overloaded
  // operator@= even when the class is POD (having a user-defined operator does
  // not make the class non-POD).  Only a plain `=` of a POD class uses the
  // implicit copy/move assignment below.  Without this, a POD class with a
  // user-defined compound-assignment operator took the C built-in path and was
  // rejected with e.g. "assignment 'assign_shr' not defined for types ...".
  const bool is_class_type = type0.id() == ID_struct_tag ||
                             type0.id() == ID_union_tag ||
                             type0.id() == ID_struct || type0.id() == ID_union;
  const bool needs_overloaded_operator =
    is_class_type && statement != ID_assign;

  if(cpp_is_pod(type0) && !needs_overloaded_operator)
  {
    // for structs we use the 'implicit assignment operator',
    // and therefore, it is allowed to assign to a rvalue struct.
    if(type0.id() == ID_struct_tag)
      to_binary_expr(expr).op0().set(ID_C_lvalue, true);

    c_typecheck_baset::typecheck_side_effect_assignment(expr);

    // Note that in C++ (as opposed to C), the assignment yields
    // an lvalue!
    expr.set(ID_C_lvalue, true);
    return;
  }

  // It's a non-POD.
  // Turn into an operator call

  std::string strop = "operator";

  if(statement == ID_assign)
    strop += "=";
  else if(statement == ID_assign_shl)
    strop += "<<=";
  else if(statement == ID_assign_shr)
    strop += ">>=";
  else if(statement == ID_assign_plus)
    strop += "+=";
  else if(statement == ID_assign_minus)
    strop += "-=";
  else if(statement == ID_assign_mult)
    strop += "*=";
  else if(statement == ID_assign_div)
    strop += "/=";
  else if(statement == ID_assign_mod)
    strop += "%=";
  else if(statement == ID_assign_bitand)
    strop += "&=";
  else if(statement == ID_assign_bitor)
    strop += "|=";
  else if(statement == ID_assign_bitxor)
    strop += "^=";
  else
  {
    error().source_location = expr.find_source_location();
    error() << "bad assignment operator '" << statement << "'" << eom;
    throw 0;
  }

  const cpp_namet cpp_name(strop, expr.source_location());

  // N5008 [over.match.oper]/3: for `a @= b` with a class-type left operand
  // the candidate functions are the MEMBER candidates (`T1::operator@=`)
  // and the NON-MEMBER candidates (unqualified lookup of `operator@=` in
  // the context of the expression, ignoring member functions, plus ADL).
  // Only the member form was ever tried, so a free `guard_exprt
  // &operator|=(guard_exprt &, const guard_exprt &)` -- the friend
  // operators of CBMC's own guard_exprt, and every free compound
  // assignment operator -- was "no match".  Try the member form silently
  // first; when it does not resolve, form the non-member call (its
  // diagnostics, if any, are the ones reported).

  // expr.op0() is already typechecked
  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.add_to_operands(already_typechecked_exprt{to_binary_expr(expr).op0()});

  side_effect_expr_function_callt new_expr(
    std::move(member),
    {to_binary_expr(expr).op1()},
    uninitialized_typet{},
    expr.source_location());

  // [over.match.oper]/3.2: for `=` the set of non-member candidates is
  // empty (and [over.ass]/1 requires operator= to be a member), so the
  // member form is the only one -- and its diagnostics are the ones wanted.
  if(statement == ID_assign)
  {
    typecheck_side_effect_function_call(new_expr);
    expr = new_expr;
    return;
  }

  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  try
  {
    sfinae_contextt sfinae_guard{*this};
    typecheck_side_effect_function_call(new_expr);
    expr = new_expr;
    return;
  }
  catch(int)
  {
    get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  }

  side_effect_expr_function_callt free_call(
    cpp_name.as_expr(),
    {already_typechecked_exprt{to_binary_expr(expr).op0()},
     to_binary_expr(expr).op1()},
    uninitialized_typet{},
    expr.source_location());

  typecheck_side_effect_function_call(free_call);

  expr = free_call;
}

void cpp_typecheckt::typecheck_side_effect_inc_dec(side_effect_exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "statement " << expr.get_statement()
            << " expected to have one operand" << eom;
    throw 0;
  }

  auto &op = to_unary_expr(expr).op();

  add_implicit_dereference(op);

  const typet &tmp_type = op.type();

  if(is_number(tmp_type) || tmp_type.id() == ID_pointer)
  {
    use_side_effect_as_lvalue(op);
    // standard stuff
    c_typecheck_baset::typecheck_expr_side_effect(expr);
    // [expr.pre.incr]/1, [expr.pre.decr]/1: in C++ a pre-increment or
    // pre-decrement of an lvalue of arithmetic or pointer type yields an
    // lvalue (the shared C base does not set this because in C they are
    // prvalues).  decltype((++x)) is therefore an lvalue-reference, which
    // C++20 compound-requirements (`{ ++i } -> same_as<I&>`) depend on.
    const irep_idt &st = expr.get(ID_statement);
    if(st == ID_preincrement || st == ID_predecrement)
      expr.set(ID_C_lvalue, true);
    return;
  }

  // Turn into an operator call

  std::string str_op = "operator";
  bool post = false;

  if(expr.get(ID_statement) == ID_preincrement)
    str_op += "++";
  else if(expr.get(ID_statement) == ID_predecrement)
    str_op += "--";
  else if(expr.get(ID_statement) == ID_postincrement)
  {
    str_op += "++";
    post = true;
  }
  else if(expr.get(ID_statement) == ID_postdecrement)
  {
    str_op += "--";
    post = true;
  }
  else
  {
    error().source_location = expr.find_source_location();
    error() << "bad assignment operator '" << expr.get_statement() << "'"
            << eom;
    throw 0;
  }

  const cpp_namet cpp_name(str_op, expr.source_location());

  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.add_to_operands(already_typechecked_exprt{op});

  side_effect_expr_function_callt new_expr(
    std::move(member), {}, uninitialized_typet{}, expr.source_location());

  // the odd C++ way to denote the post-inc/dec operator
  if(post)
    new_expr.arguments().push_back(
      from_integer(mp_integer(0), signed_int_type()));

  typecheck_side_effect_function_call(new_expr);
  expr.swap(new_expr);
}

void cpp_typecheckt::typecheck_expr_dereference(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "unary operator * expects one operand" << eom;
    throw 0;
  }

  exprt &op = to_dereference_expr(expr).pointer();
  const typet &op_type = op.type();

  if(op_type.id() == ID_pointer && op_type.find(ID_to_member).is_not_nil())
  {
    error().source_location = expr.find_source_location();
    error() << "pointer-to-member must use "
            << "the .* or ->* operators" << eom;
    throw 0;
  }

  c_typecheck_baset::typecheck_expr_dereference(expr);
}

void cpp_typecheckt::convert_pmop(exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_to_member);
  PRECONDITION(expr.operands().size() == 2);

  auto &op0 = to_binary_expr(expr).op0();
  auto &op1 = to_binary_expr(expr).op1();

  if(op1.type().id() != ID_pointer || op1.type().find(ID_to_member).is_nil())
  {
    error().source_location = expr.source_location();
    error() << "pointer-to-member expected" << eom;
    throw 0;
  }

  typet t0 = op0.type().id() == ID_pointer
               ? to_pointer_type(op0.type()).base_type()
               : op0.type();

  typet t1((const typet &)op1.type().find(ID_to_member));

  if(t0.id() != ID_struct_tag)
  {
    error().source_location = expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  const struct_typet &from_struct = follow_tag(to_struct_tag_type(t0));
  const struct_typet &to_struct = follow_tag(to_struct_tag_type(t1));

  if(!subtype_typecast(from_struct, to_struct))
  {
    error().source_location = expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  // (the synthesised declval<>() operand of an __is_invocable probe is
  // already typed and has no expression form to re-check)
  if(op1.id() != ID_nondet_symbol)
    typecheck_expr_main(op1);

  if(op0.type().id() != ID_pointer)
  {
    if(op0.id() == ID_dereference)
    {
      op0 = to_dereference_expr(op0).pointer();
      // N5008 [expr.mptr.oper]/3: the object expression's REFERENCE type
      // is not part of the bound object -- a call `ref().*pmf` whose
      // operand is a function returning `S&` (the front end's
      // dereference of a reference-typed pointer) binds a plain `S*`.
      // Keeping the reference flag made the implicit `this` conversion
      // reject "S& to S*" (libstdc++ `__invoke_memfun_deref`:
      // `((*std::forward<_Tp>(__t)).*__f)(...)`, every std::bind over a
      // member function pointer).
      if(
        op0.type().id() == ID_pointer &&
        (op0.type().get_bool(ID_C_reference) ||
         op0.type().get_bool(ID_C_rvalue_reference)))
      {
        typet plain = op0.type();
        plain.remove(ID_C_reference);
        plain.remove(ID_C_rvalue_reference);
        op0 = typecast_exprt{op0, plain};
      }
    }
    else
    {
      DATA_INVARIANT(
        op0.get_bool(ID_C_lvalue),
        "pointer-to-member must have lvalue operand");
      op0 = address_of_exprt(op0);
    }
  }

  // N5008 [expr.mptr.oper]/2: for a pointer to DATA member, E1.*E2 is the
  // member of E1 that E2 designates -- at E2's offset (see
  // typecheck_expr_address_of) within E1's subobject of E2's class;
  // /3: E1->*E2 is (*(E1)).*E2; /5: the cv-qualifiers combine as for E1.E2;
  // /6: the result is an lvalue (an xvalue for an rvalue E1, which the
  // front end does not distinguish).
  if(to_pointer_type(op1.type()).base_type().id() != ID_code)
  {
    const struct_tag_typet &member_class = to_struct_tag_type(t1);
    exprt object_pointer = op0;
    const typet &object_class =
      to_pointer_type(object_pointer.type()).base_type();
    const bool object_const = object_class.get_bool(ID_C_constant);
    if(
      object_class.id() == ID_struct_tag &&
      to_struct_tag_type(object_class).get_identifier() !=
        member_class.get_identifier())
    {
      // [expr.mptr.oper]/2: the member class is a base of the object's
      make_ptr_typecast(object_pointer, pointer_type(member_class));
    }
    typet member_type = to_pointer_type(op1.type()).base_type();
    if(object_const)
      member_type.set(ID_C_constant, true);
    const exprt offset = minus_exprt{
      typecast_exprt{op1, signed_size_type()},
      from_integer(data_member_pointer_bias(), signed_size_type())};
    const exprt address = typecast_exprt{
      plus_exprt{
        typecast_exprt{object_pointer, pointer_type(char_type())}, offset},
      pointer_type(member_type)};
    dereference_exprt member{address, member_type};
    member.set(ID_C_lvalue, true);
    member.add_source_location() = expr.source_location();
    expr.swap(member);
    return;
  }

  exprt tmp(op1);
  tmp.type().set(ID_C_bound, op0);
  expr.swap(tmp);
  return;
}

void cpp_typecheckt::typecheck_expr_function_identifier(exprt &expr)
{
  // [basic.def.odr]/5, [temp.inst]/4: a function named only in an
  // unevaluated operand is not odr-used; its definition is instantiated
  // only if an odr-use follows (release_referenced_held_back_bodies and the
  // deferred-body drain find that use)
  if(expr.id() == ID_symbol && unevaluated_operand_depth == 0)
  {
    // Check if the function body has to be typechecked
    symbolt &function_symbol =
      symbol_table.get_writeable_ref(expr.get(ID_identifier));

    if(function_symbol.value.id() == ID_cpp_not_typechecked)
      function_symbol.value.set(ID_is_used, true);

    // For functions in deferred_typechecking (e.g., static member
    // functions of class templates), ensure the body gets typechecked
    // by adding it to method_bodies.
    if(
      function_symbol.value.is_not_nil() &&
      deferred_typechecking.count(function_symbol.name))
    {
      add_method_body(&function_symbol);
    }

    {
      auto it = deferred_method_bodies.find(function_symbol.name);
      if(it != deferred_method_bodies.end())
      {
        method_bodies.push_back(std::move(it->second));
        deferred_method_bodies.erase(it);
      }
    }
  }

  c_typecheck_baset::typecheck_expr_function_identifier(expr);
}

void cpp_typecheckt::typecheck_expr(exprt &expr, const target_typet &target)
{
  // Phase 2 of the target-type-threading refactor.
  //
  // [temp.deduct.funcaddr]/1: a cpp_name argument bound to a
  // pointer-to-function parameter — either as a bare cpp_name
  // (implicit function-to-pointer per [conv.func]/1) or as an
  // explicit `&cpp_name` — drives template-argument deduction
  // forward from the target.  On success, swap in the typed
  // `address_of(specialisation)`; on failure, fall through to the
  // isolated path so real mismatches surface as user-visible
  // errors.
  if(target.has_target())
  {
    const bool is_funcaddr_shape =
      expr.id() == ID_cpp_name ||
      (expr.id() == ID_address_of && expr.operands().size() == 1 &&
       to_unary_expr(expr).op().id() == ID_cpp_name);

    if(is_funcaddr_shape)
    {
      exprt deduced = deduce_funcaddr_against_target(expr, *target.get());
      if(deduced.is_not_nil())
      {
        expr.swap(deduced);
        return;
      }
    }
  }

  // Fall through to the no-target implementation.
  typecheck_expr(expr);
}

void cpp_typecheckt::typecheck_expr(exprt &expr)
{
  // Re-type-check guard for an already-elaborated implicit dereference of a
  // reference ([dcl.ref]/1, [expr.unary.op]/1: the built-in unary `*` applied
  // to a reference operand denotes the object the reference is bound to).  A
  // reference lvalue -- most notably an access to a reference data member
  // `this->ref` -- is materialised by `add_implicit_dereference` as an implicit
  // `dereference_exprt` whose operand keeps the reference type.  Such a node is
  // fully type-checked when it is built (by `typecheck_expr_member` during name
  // resolution) and is never re-elaborated in the normal flow, but the exact
  // same sub-tree can reach `typecheck_expr` a second time -- e.g. a
  // braced-init-list call argument like `g({ref})` is type-checked once by the
  // operand walk and again while the call's arguments are converted to the
  // parameter type.  The generic operand walk (`typecheck_expr_operands`, run
  // before `typecheck_expr_main`) would re-type-check the operand `this->ref`,
  // whose member access re-applies its own implicit dereference; the outer `*`
  // then wraps the already-dereferenced value, corrupting `*this->ref` into the
  // ill-formed `*(*this->ref)` and tripping "operand of unary * ... is not a
  // pointer".  Since the node is already well-formed (it carries its
  // non-reference result type), leave it untouched before the operands are
  // walked.
  if(
    expr.id() == ID_dereference && expr.get_bool(ID_C_implicit) &&
    expr.operands().size() == 1 && expr.type().is_not_nil() &&
    is_reference(to_unary_expr(expr).op().type()))
  {
    return;
  }

  bool override_constantness = expr.get_bool(ID_C_override_constantness);

  // N5008 [expr.prim.req.general]/3-4: the parameters of a
  // requires-expression (`requires(S s) { s.x; }') are in scope in its
  // requirements.  The parser attaches them to the expression
  // (#requires_params); the concept-evaluation path binds them itself,
  // but a requires-expression elsewhere -- a namespace-scope
  // `static_assert(requires(S s) { s.x; })' -- reached this point with the
  // parameters unbound, so every requirement naming one was "invalid" and
  // the assertion failed.  Bind them in a scope of their own.
  if(expr.find("#requires_params").is_not_nil())
  {
    const irept params = expr.find("#requires_params");
    expr.remove("#requires_params");
    cpp_save_scopet saved_scope(cpp_scopes);
    cpp_scopes.new_block_scope();
    for(const auto &param : params.get_sub())
    {
      const irep_idt pname = param.get(ID_name);
      if(pname.empty())
        continue;
      typet ptype = static_cast<const typet &>(param.find(ID_type));
      if(bind_requires_parameter_pack(pname, ptype))
        continue;
      typecheck_type(ptype);
      bind_requires_parameter(pname, ptype);
    }
    typecheck_expr(expr);
    return;
  }

  // We take care of an ambiguity in the C++ grammar.
  // Needs to be done before the operands!
  unary_operand_typecast_ambiguity(expr);
  explicit_typecast_ambiguity(expr);

  // cpp_name uses get_sub, which can get confused with expressions.
  if(expr.id() == ID_cpp_name)
    typecheck_expr_cpp_name(expr, cpp_typecheck_fargst());
  else if(is_qualified_member_address(expr))
  {
    // N5008 [expr.unary.op]/4: `&C::m' with a qualified-id naming a
    // non-static member forms a pointer to member even where `this' is
    // available (a member function, a default member initializer); only
    // `&m' and the parenthesized `&(C::m)' denote the object's member.  The
    // resolver turns a member name into `this->m' whenever the scope has a
    // `this', so resolve the operand without it: it then yields the
    // pointer-to-member form (the `cpp-this' placeholder, see
    // typecheck_expr_address_of).
    exprt &scope_this = cpp_scopes.current_scope().this_expr;
    exprt saved_this = scope_this;
    scope_this.make_nil();
    try
    {
      typecheck_expr(to_unary_expr(expr).op());
    }
    catch(...)
    {
      scope_this = saved_this;
      throw;
    }
    scope_this = saved_this;
    typecheck_expr_main(expr);
  }
  else if(expr.id() == "lambda")
    typecheck_expr_lambda(expr);
  else if(expr.id() == ID_arguments)
  {
    expand_type_pack_arguments(expr);
    // Arguments list for a function call.  Typecheck each argument
    // individually, catching and deferring failures: an argument
    // of the form `&f` or `f` where `f` names a function template
    // cannot be typechecked in isolation here because the deduction
    // needs the outer call's parameter types
    // ([temp.deduct.funcaddr]).  Leave such arguments untyped so
    // the containing typecheck_side_effect_function_call can retry
    // them with target-type context.  For arguments with an already
    // typechecked body (`ID_already_typechecked`) just continue; for
    // all others, attempt the full typecheck and let any C++
    // exception propagate unless the operand is a function-address
    // candidate we can retry later.
    for(auto &op : expr.operands())
    {
      const bool may_need_target_type = [&]() -> bool
      {
        const exprt *probe = &op;
        if(probe->id() == ID_address_of && probe->operands().size() == 1)
          probe = &to_unary_expr(*probe).op();
        return probe->id() == ID_cpp_name;
      }();

      if(!may_need_target_type)
      {
        typecheck_expr(op);
        continue;
      }

      // Function-address template candidate — try, but defer on failure.
      try
      {
        typecheck_expr(op);
      }
      catch(...)
      {
        op.type().make_nil();
      }
    }
  }
  else if(
    expr.id() == "simple_requirement" || expr.id() == "compound_requirement" ||
    expr.id() == "type_requirement")
  {
    // [expr.prim.req.general]/5 with [expr.prim.req.simple]/1,
    // [expr.prim.req.compound]/1 and [expr.prim.req.type]/1: the
    // sub-expression (or type) named by a requirement is checked for
    // *validity* in the immediate context -- an invalid expression or type
    // makes the enclosing requires-expression evaluate to false, it is not an
    // ill-formed program.  It must therefore not be typechecked by the
    // ordinary operand recursion below (which would emit a hard error for,
    // e.g., `a + a` on a class type without operator+, before the requirement
    // handler can soften it).  Dispatch straight to typecheck_expr_main, which
    // evaluates the requirement under an sfinae_contextt and converts any
    // failure to a soft `false`.
    typecheck_expr_main(expr);
  }
  else
  {
    // This does the operands, and then calls typecheck_expr_main.
    c_typecheck_baset::typecheck_expr(expr);
  }

  if(override_constantness)
    expr.type().set(ID_C_constant, false);
}

bool cpp_typecheckt::is_qualified_member_address(const exprt &expr)
{
  if(
    expr.id() != ID_address_of || expr.operands().size() != 1 ||
    to_unary_expr(expr).op().id() != ID_cpp_name ||
    to_unary_expr(expr).op().get_bool(ID_C_parenthesized) ||
    !to_cpp_name(to_unary_expr(expr).op()).is_qualified())
  {
    return false;
  }
  return cpp_scopes.current_scope().this_expr.is_not_nil();
}

void cpp_typecheckt::explicit_typecast_ambiguity(exprt &expr)
{
  // There is an ambiguity in the C++ grammar as follows:
  // (TYPENAME) + expr   (typecast of unary plus)  vs.
  // (expr) + expr       (sum of two expressions)
  // Same issue with the operators & and - and *

  // We figure this out by resolving the type argument
  // and re-writing if needed

  if(expr.id() != "explicit-typecast")
    return;

  PRECONDITION(expr.operands().size() == 1);

  irep_idt op0_id = to_unary_expr(expr).op().id();

  if(
    expr.type().id() == ID_cpp_name &&
    to_unary_expr(expr).op().operands().size() == 1 &&
    (op0_id == ID_unary_plus || op0_id == ID_unary_minus ||
     op0_id == ID_address_of || op0_id == ID_dereference))
  {
    exprt resolve_result = resolve(
      to_cpp_name(expr.type()),
      cpp_typecheck_resolvet::wantt::BOTH,
      cpp_typecheck_fargst());

    if(resolve_result.id() != ID_type)
    {
      // need to re-write the expression
      // e.g., (ID) +expr  ->  ID+expr
      exprt new_binary_expr;

      new_binary_expr.operands().resize(2);
      to_binary_expr(new_binary_expr).op0().swap(expr.type());
      to_binary_expr(new_binary_expr)
        .op1()
        .swap(to_unary_expr(to_unary_expr(expr).op()).op());

      if(op0_id == ID_unary_plus)
        new_binary_expr.id(ID_plus);
      else if(op0_id == ID_unary_minus)
        new_binary_expr.id(ID_minus);
      else if(op0_id == ID_address_of)
        new_binary_expr.id(ID_bitand);
      else if(op0_id == ID_dereference)
        new_binary_expr.id(ID_mult);

      new_binary_expr.add_source_location() =
        to_unary_expr(expr).op().source_location();
      new_binary_expr.set(ID_C_explicit_typecast_rewrite, true);
      expr.swap(new_binary_expr);
    }
  }
}

/// N5008 [expr.cast]/2, [dcl.ambig.res]: `(x) & m' is a cast only if x
/// names a type.  The parser took `*(wp) & m' as `*' applied to the cast
/// `(wp) &m'; when explicit_typecast_ambiguity turns that operand into the
/// binary `wp & m', the prefix operator -- which binds tighter than any of
/// the binary operators involved ([expr.unary.op]) -- applies to `(wp)'
/// only: `(*wp) & m'.  Rotate it into the left operand.  libstdc++'s
/// bitset::reference `(*(_M_wp) & _Base::_S_maskbit(_M_bpos))'.
void cpp_typecheckt::unary_operand_typecast_ambiguity(exprt &expr)
{
  static const std::set<irep_idt> prefix_operators{
    ID_dereference,
    ID_unary_minus,
    ID_unary_plus,
    ID_not,
    ID_bitnot,
    ID_address_of};
  if(expr.operands().size() != 1 || prefix_operators.count(expr.id()) == 0)
    return;
  exprt &op = to_unary_expr(expr).op();
  unary_operand_typecast_ambiguity(op);
  explicit_typecast_ambiguity(op);
  if(!op.get_bool(ID_C_explicit_typecast_rewrite) || op.operands().size() != 2)
  {
    return;
  }
  // unary(lhs OP rhs) -> unary(lhs) OP rhs
  exprt binary = op;
  exprt unary = expr;
  to_unary_expr(unary).op() = to_binary_expr(binary).op0();
  to_binary_expr(binary).op0() = std::move(unary);
  expr.swap(binary);
}

void cpp_typecheckt::typecheck_expr_binary_arithmetic(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.find_source_location();
    error() << "operator '" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  add_implicit_dereference(to_binary_expr(expr).op0());
  add_implicit_dereference(to_binary_expr(expr).op1());

  c_typecheck_baset::typecheck_expr_binary_arithmetic(expr);

  // N5008 [expr.type]/2: a prvalue of a non-class, non-array type has a
  // cv-unqualified type.  Pointer arithmetic takes its result type from the
  // pointer operand; when that operand is a `const`-qualified glvalue
  // (`declval<const I>() + n` with I = int*, the shape of the
  // random_access_iterator requirement `{ __j + __n } -> same_as<_Iter>`)
  // the qualifier leaked into the result (`int *const`).
  if(
    !expr.get_bool(ID_C_lvalue) && expr.type().id() != ID_struct_tag &&
    expr.type().id() != ID_union_tag && expr.type().id() != ID_array &&
    (expr.type().get_bool(ID_C_constant) ||
     expr.type().get_bool(ID_C_volatile)))
  {
    expr.type().remove(ID_C_constant);
    expr.type().remove(ID_C_volatile);
  }
}

void cpp_typecheckt::typecheck_expr_index(exprt &expr)
{
  c_typecheck_baset::typecheck_expr_index(expr);
}

void cpp_typecheckt::typecheck_expr_comma(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.find_source_location();
    error() << "comma operator expects two operands" << eom;
    throw 0;
  }

  const auto &op0_type = to_binary_expr(expr).op0().type();

  if(op0_type.id() == ID_struct || op0_type.id() == ID_struct_tag)
  {
    // TODO: check if the comma operator has been overloaded!
  }

  c_typecheck_baset::typecheck_expr_comma(expr);
}

void cpp_typecheckt::typecheck_expr_rel(binary_relation_exprt &expr)
{
  // N5008 [expr.eq]/3, [expr.rel]/3, [expr.type]/4: pointers to classes C1
  // and C2, C1 derived from C2, are compared after converting both to the
  // composite pointer type, pointer to (cv-combined) C2 -- the
  // derived-to-base conversion adjusts the pointer to the base subobject;
  // the C rule below casts the representation unchanged
  for(int k = 0; k < 2; ++k)
  {
    exprt &from = k == 0 ? expr.op0() : expr.op1();
    const exprt &to = k == 0 ? expr.op1() : expr.op0();
    if(
      from.type().id() != ID_pointer || to.type().id() != ID_pointer ||
      is_reference(from.type()) || is_reference(to.type()))
    {
      continue;
    }
    const typet &from_base = to_pointer_type(from.type()).base_type();
    const typet &to_base = to_pointer_type(to.type()).base_type();
    if(
      from_base.id() != ID_struct_tag || to_base.id() != ID_struct_tag ||
      to_struct_tag_type(from_base).get_identifier() ==
        to_struct_tag_type(to_base).get_identifier())
    {
      continue;
    }
    const struct_typet &from_struct = follow_tag(to_struct_tag_type(from_base));
    const struct_typet &to_struct = follow_tag(to_struct_tag_type(to_base));
    if(!subtype_typecast(from_struct, to_struct))
      continue;
    // the composite type's pointee keeps the qualifiers of both
    pointer_typet composite = to_pointer_type(to.type());
    if(from_base.get_bool(ID_C_constant))
      composite.base_type().set(ID_C_constant, true);
    if(from_base.get_bool(ID_C_volatile))
      composite.base_type().set(ID_C_volatile, true);
    make_ptr_typecast(from, composite);
    break;
  }

  c_typecheck_baset::typecheck_expr_rel(expr);

  // Ensure both operands of pointer comparisons have exactly the same
  // type. The C type-checker creates null_pointer_exprt with the right
  // base type, but pointer annotations (e.g., #to_member for
  // pointer-to-member-function) may differ. Force the rhs type to
  // match the lhs type when both are pointers.
  if(
    expr.op0().type().id() == ID_pointer &&
    expr.op1().type().id() == ID_pointer &&
    expr.op0().type() != expr.op1().type())
  {
    expr.op1() = typecast_exprt(expr.op1(), expr.op0().type());
  }
}

/// N5008 [expr.prim.this]/2, [class.mfct.non.static]/2: in the body \p body
/// of a lambda that captures `this', an explicit `this' and an unqualified
/// call of a member function of the enclosing class (one of
/// \p member_functions) refer to the enclosing object.  The closure holds
/// that pointer in its member lambda_this_capture; rewrite `this' to that
/// member and `f(...)' to `lambda_this_capture->f(...)'.  Nested lambdas
/// are not rewritten (they are type-checked on their own), nor are names
/// after `.' or `->' (component names).
void cpp_typecheckt::rewrite_lambda_this_uses(
  irept &body,
  const std::set<irep_idt> &member_functions)
{
  const auto this_member = [](const source_locationt &location)
  {
    exprt name{ID_cpp_name};
    irept component{ID_name};
    component.set(ID_identifier, lambda_this_capture);
    component.add(ID_C_source_location) = location;
    name.get_sub().push_back(std::move(component));
    name.add_source_location() = location;
    return name;
  };
  std::function<void(irept &)> rewrite = [&](irept &node)
  {
    if(node.id() == ID_lambda)
      return;
    if(node.id() == "cpp-this")
    {
      const source_locationt location =
        static_cast<const exprt &>(node).source_location();
      node = this_member(location);
      return;
    }
    if(
      node.id() == ID_side_effect &&
      node.get(ID_statement) == ID_function_call && !node.get_sub().empty())
    {
      irept &callee = node.get_sub().front();
      if(
        callee.id() == ID_cpp_name && !callee.get_sub().empty() &&
        callee.get_sub().front().id() == ID_name &&
        member_functions.count(callee.get_sub().front().get(ID_identifier)) !=
          0 &&
        (callee.get_sub().size() == 1 ||
         (callee.get_sub().size() == 2 &&
          callee.get_sub()[1].id() == ID_template_args)))
      {
        const source_locationt location =
          static_cast<const exprt &>(callee).source_location();
        exprt member{ID_ptrmember};
        member.add_to_operands(this_member(location));
        member.add(ID_component_cpp_name) = callee;
        member.add_source_location() = location;
        callee = std::move(member);
      }
    }
    for(auto &sub : node.get_sub())
      rewrite(sub);
    for(auto &named : node.get_named_sub())
    {
      if(named.first != ID_component_cpp_name)
        rewrite(named.second);
    }
  };
  rewrite(body);
}

void cpp_typecheckt::typecheck_expr_lambda(exprt &expr)
{
  // Lower C++11 lambda by creating a function where captured variables
  // become local constants initialized to their capture-point values.
  // The lambda becomes a function pointer.

  static unsigned lambda_count = 0;
  const std::string lambda_id = "__lambda_" + std::to_string(lambda_count++);
  const source_locationt &loc = expr.source_location();
  const std::string func_sym_name =
    id2string(cpp_scopes.current_scope().prefix) + lambda_id;

  // [expr.prim.lambda.closure]/1: a lambda has a unique closure *class* type.
  // For a captureless, non-generic lambda we additionally synthesise that
  // closure class (a struct with operator() and a conversion to function
  // pointer) so the lambda can be used as an object -- e.g. stored by value in
  // std::function -- not only as a function pointer.  Capture the
  // pre-type-check parameters/body now, before the function-lowering below
  // mutates the expression.  (Capturing and generic lambdas keep the
  // function-pointer lowering for now; see
  // doc/architectural/cpp-lambda-closure-support.md.)
  const bool lambda_is_captureless =
    expr.find("lambda_capture").get_sub().empty() &&
    expr.find("lambda_capture").get("default").empty();
  const irept saved_lambda_parameters = expr.find(ID_parameters);
  const irept saved_lambda_body = expr.find("body");
  const irept saved_lambda_return_type = expr.find(ID_return_type);
  // A C++23 deducing-this lambda has an explicit object parameter; keep it on
  // the function-pointer lowering for now (Phase A is captureless,
  // non-generic, implicit-object lambdas).
  bool lambda_has_explicit_this = false;
  for(const auto &p : saved_lambda_parameters.get_sub())
    if(p.get_bool("explicit_this"))
      lambda_has_explicit_this = true;
  // Phases B/C/D/E handle explicit by-copy/by-reference captures, mutable
  // lambdas, capture-defaults (`[=]`/`[&]`), and -- in a member-function
  // context -- this/*this capture modelled as captures of the odr-used data
  // members (by reference for `this`/`[=]`/`[&]`, by copy for `[*this]`).  A
  // member-function-context lambda that uses `this` explicitly or odr-uses a
  // member function, a C++23 deducing-this lambda, generic lambdas, and a body
  // containing a nested lambda stay on the function-pointer lowering for now
  // (see doc/architectural/cpp-lambda-closure-support.md).
  const bool lambda_is_mutable = expr.get_bool("mutable");
  const exprt lambda_enclosing_this = cpp_scopes.current_scope().this_expr;
  const bool lambda_in_member_context = lambda_enclosing_this.is_not_nil();
  bool lambda_has_star_this = false;
  for(const auto &cap : expr.find("lambda_capture").get_sub())
    if(cap.get_bool("this") && cap.get_bool("star_this"))
      lambda_has_star_this = true;
  // A lambda whose body returns/contains another lambda has a closure-typed
  // return; the function-pointer lowering's deduced return type is then not
  // usable for the synthesised operator().  Keep such a lambda on the
  // function-pointer lowering for now; the nested lambda itself still uses the
  // closure path (later phases handle returned/escaping closures uniformly).
  bool lambda_body_has_nested_lambda = false;
  {
    std::function<void(const irept &)> scan = [&](const irept &node)
    {
      if(node.id() == "lambda")
        lambda_body_has_nested_lambda = true;
      for(const auto &s : node.get_sub())
        scan(s);
      for(const auto &n : node.get_named_sub())
        scan(n.second);
    };
    scan(saved_lambda_body);
  }

  // Check for C++14 generic lambda (auto parameters) or
  // C++20 template lambda (unresolved type name parameters)
  bool is_generic_lambda = false;
  {
    const irept &check_params = expr.find(ID_parameters);
    // N5008 [expr.prim.lambda.general]/4: a lambda is generic iff it has an
    // explicit template-parameter-list or a parameter of (possibly
    // cv-/ref-qualified) type `auto`.  A parameter whose type is written as a
    // plain name is generic ONLY when that name is a template parameter (e.g.
    // the `T` of `[]<class T>(T)`), NOT when it names a concrete type (e.g.
    // `[](E &x)` for a class E).  Misclassifying an ordinary class-name
    // parameter as generic replaces it with `signed int` below, so a body that
    // accesses a member of the parameter fails with "member operator requires
    // struct/union type ... but got 'signed int'".  Decide genericity by
    // resolving a cpp_name parameter type: a concrete type means not generic.
    auto is_generic_param_type = [&](const typet &pt) -> bool
    {
      if(has_auto(pt) || pt.id() == ID_auto)
        return true;
      if(pt.id() != ID_cpp_name)
        return false;
      cpp_save_scopet save_scope(cpp_scopes);
      cpp_typecheck_resolvet resolver(*this);
      exprt r = resolver.resolve(
        to_cpp_name(static_cast<const irept &>(pt)),
        cpp_typecheck_resolvet::wantt::TYPE,
        cpp_typecheck_fargst{},
        false);
      // Unresolved, or resolved to a (dependent) template parameter -> generic.
      return r.is_nil() || (r.id() == ID_type &&
                            r.type().id() == ID_template_parameter_symbol_type);
    };

    for(const auto &p : check_params.get_sub())
    {
      const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
      if(pdecl.get_bool("explicit_this"))
        continue;
      if(is_generic_param_type(pdecl.type()))
      {
        is_generic_lambda = true;
        break;
      }
    }

    if(is_generic_lambda)
    {
      generic_lambda_map[func_sym_name] = expr;

      // Replace auto/template parameters with signed int
      irept &default_params = expr.add(ID_parameters);
      for(auto &p : default_params.get_sub())
      {
        cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
        if(pdecl.get_bool("explicit_this"))
          continue;
        if(is_generic_param_type(pdecl.type()))
          replace_auto_in_type(pdecl.type(), signed_int_type());
      }
    }
  }

  // Collect captures
  const irept &capture_list = expr.find("lambda_capture");
  std::map<irep_idt, exprt> capture_values;
  std::set<irep_idt> by_ref_captures;
  for(const auto &cap : capture_list.get_sub())
  {
    irep_idt cap_name = cap.get(ID_identifier);
    if(cap_name.empty())
      continue;

    if(cap.get_bool("by_ref"))
      by_ref_captures.insert(cap_name);

    // C++14 init-capture: [y = expr]
    const exprt &init = static_cast<const exprt &>(cap.find("init"));
    if(init.is_not_nil())
    {
      exprt init_copy = init;
      typecheck_expr(init_copy);
      capture_values[cap_name] = init_copy;
    }
    else
    {
      exprt cap_expr(ID_cpp_name);
      irept name_node(ID_name);
      name_node.set(ID_identifier, cap_name);
      cap_expr.get_sub().push_back(name_node);
      cap_expr.add_source_location() = loc;
      typecheck_expr(cap_expr);
      capture_values[cap_name] = cap_expr;
    }
  }

  // Capture-default ([=] or [&]): [expr.prim.lambda.capture] -- each entity
  // with automatic storage duration that is odr-used in the body and not
  // explicitly captured is captured (by copy for '=', by reference for '&').
  // We approximate odr-use by collecting the simple-identifier names appearing
  // in the body and capturing those that resolve, in the lambda's enclosing
  // scope, to an automatic local variable.  (Over-approximation -- e.g. a name
  // shadowed by a body-local -- yields at worst an unused capture member.)
  const irep_idt capture_default = capture_list.get("default");
  if(!capture_default.empty())
  {
    const bool default_by_ref = capture_default == "&";

    // The lambda's own parameters are not captures.
    std::set<irep_idt> param_names;
    for(const auto &p : expr.find(ID_parameters).get_sub())
    {
      if(p.id() != ID_cpp_declaration)
        continue;
      const auto &pd = to_cpp_declaration(static_cast<const exprt &>(p));
      if(pd.declarators().empty())
        continue;
      const auto &ns = pd.declarators().front().name().get_sub();
      if(!ns.empty())
        param_names.insert(ns.front().get(ID_identifier));
    }

    std::set<irep_idt> candidates;
    std::function<void(const irept &)> scan = [&](const irept &node)
    {
      if(
        node.id() == ID_cpp_name && node.get_sub().size() == 1 &&
        node.get_sub().front().id() == ID_name)
        candidates.insert(node.get_sub().front().get(ID_identifier));
      for(const auto &s : node.get_sub())
        scan(s);
      for(const auto &n : node.get_named_sub())
        scan(n.second);
    };
    scan(saved_lambda_body);

    for(const irep_idt &name : candidates)
    {
      if(name.empty() || capture_values.count(name) || param_names.count(name))
        continue;
      const auto ids =
        cpp_scopes.current_scope().lookup(name, cpp_scopet::RECURSIVE);
      for(const auto *id_ptr : ids)
      {
        if(id_ptr->id_class != cpp_idt::id_classt::SYMBOL)
          continue;
        const symbolt *sym = symbol_table.lookup(id_ptr->identifier);
        if(
          sym == nullptr || !sym->is_lvalue || sym->is_static_lifetime ||
          sym->is_type || sym->type.id() == ID_code)
          continue;
        // An automatic local variable odr-used under a capture-default.
        exprt cap_expr(ID_cpp_name);
        irept name_node(ID_name);
        name_node.set(ID_identifier, name);
        cap_expr.get_sub().push_back(name_node);
        cap_expr.add_source_location() = loc;
        typecheck_expr(cap_expr);
        capture_values[name] = cap_expr;
        if(default_by_ref)
          by_ref_captures.insert(name);
        break;
      }
    }
  }

  // this/*this capture in a member-function context.
  // [expr.prim.lambda.capture]
  // / [expr.prim.lambda.closure]: `[this]` (and a capture-default that odr-uses
  // members) captures the enclosing object by reference; `[*this]` captures it
  // by copy.  We model this as captures of the odr-used non-static data members
  // of the enclosing class -- by reference for `this`/`[=]`/`[&]` (the live
  // object) or by copy for `[*this]` (a snapshot) -- so the existing closure
  // lowering handles them and the member odr-uses in the body resolve to the
  // capture members.  An explicit use of `this` or an odr-use of a member
  // function cannot be modelled this way; such lambdas stay on the
  // function-pointer lowering.
  bool member_context_unsupported = false;
  // N5008 [expr.prim.this]/2, [expr.prim.lambda.capture]/8, /10: in the body
  // of a lambda that captures `this' by reference ([this], or a
  // capture-default that odr-uses it), `this' and the implicit object of an
  // unqualified member function call ([class.mfct.non.static]/2) are the
  // enclosing object.  The closure keeps the captured pointer in a member
  // named lambda_this_capture; the body's explicit `this' and those calls
  // are rewritten to use it (rewrite_lambda_this_uses).
  bool lambda_needs_this_pointer = false;
  std::set<irep_idt> lambda_member_function_names;
  if(lambda_in_member_context)
  {
    if(
      lambda_enclosing_this.type().id() == ID_pointer &&
      to_pointer_type(lambda_enclosing_this.type()).base_type().id() ==
        ID_struct_tag)
    {
      std::set<irep_idt> candidates;
      bool uses_explicit_this = false;
      std::function<void(const irept &)> scan = [&](const irept &node)
      {
        if(node.id() == "cpp-this")
          uses_explicit_this = true;
        if(
          node.id() == ID_cpp_name && node.get_sub().size() == 1 &&
          node.get_sub().front().id() == ID_name)
          candidates.insert(node.get_sub().front().get(ID_identifier));
        for(const auto &s : node.get_sub())
          scan(s);
        for(const auto &n : node.get_named_sub())
          scan(n.second);
      };
      scan(saved_lambda_body);

      if(uses_explicit_this)
      {
        if(lambda_has_star_this)
          member_context_unsupported = true;
        else
          lambda_needs_this_pointer = true;
      }

      const struct_typet &enclosing_struct = this_struct_type();
      std::vector<irep_idt> member_captures;
      for(const irep_idt &name : candidates)
      {
        if(name.empty() || capture_values.count(name))
          continue;
        const struct_typet::componentt *comp = nullptr;
        for(const auto &c : enclosing_struct.components())
          if(c.get_base_name() == name)
          {
            comp = &c;
            break;
          }
        if(comp == nullptr)
        {
          // Not a data member or member function component.  A member
          // TEMPLATE of the enclosing class is not a struct component
          // at all -- it lives only in the class SCOPE -- yet an
          // unqualified call to it in the body is, per N5008
          // [class.mfct.non.static]/3, `(*this).name(...)` on the
          // ENCLOSING object, and [expr.prim.lambda.capture]/8 makes
          // the capture-default capture that `this`.  Treated as "not
          // a member", the closure path resolved the call against the
          // closure's own `this`, the implicit-object conversion
          // threw, and the body was silently dropped (libc++
          // vector::emplace_back's `[&] { __emplace_back_slow_path(
          // std::forward<_Args>(__args)...); }`).  Route it the same
          // way as a member function odr-use.
          const irep_idt &enclosing_id = enclosing_struct.get(ID_name);
          if(
            !enclosing_id.empty() &&
            cpp_scopes.id_map.find(enclosing_id) != cpp_scopes.id_map.end())
          {
            const auto tmpl_hits =
              cpp_scopes.get_scope(enclosing_id)
                .lookup(
                  name, cpp_scopet::QUALIFIED, cpp_idt::id_classt::TEMPLATE);
            if(!tmpl_hits.empty())
            {
              if(lambda_has_star_this)
                member_context_unsupported = true;
              else
              {
                lambda_needs_this_pointer = true;
                lambda_member_function_names.insert(name);
              }
            }
          }
          continue;
        }
        if(comp->type().id() == ID_code)
        {
          // odr-use of a member function: called through the captured
          // `this' (not modellable as a data-member capture of a copy)
          if(lambda_has_star_this)
            member_context_unsupported = true;
          else
          {
            lambda_needs_this_pointer = true;
            lambda_member_function_names.insert(name);
          }
          continue;
        }
        member_captures.push_back(name);
      }

      // Only materialise the member captures if the whole lambda is modellable
      // on the closure path (otherwise the function-pointer lowering is used,
      // and capture_values must not be polluted with member accesses).
      if(!member_context_unsupported)
      {
        const bool member_by_ref = !lambda_has_star_this;
        for(const irep_idt &name : member_captures)
        {
          exprt cap_expr(ID_cpp_name);
          irept name_node(ID_name);
          name_node.set(ID_identifier, name);
          cap_expr.get_sub().push_back(name_node);
          cap_expr.add_source_location() = loc;
          typecheck_expr(cap_expr);
          capture_values[name] = cap_expr;
          if(member_by_ref)
            by_ref_captures.insert(name);
        }
        // the captured `this' itself, a pointer copied into the closure
        if(lambda_needs_this_pointer)
          capture_values[lambda_this_capture] = lambda_enclosing_this;
      }
    }
    else
      member_context_unsupported = true;
  }

  // A generic lambda is lowered to a closure with a member function template
  // operator() (Phase F) unless it has an explicit object parameter, uses
  // `this' explicitly or odr-uses a member function (member_context_
  // unsupported), or its body contains a nested lambda -- those keep the
  // call-site instantiation (function-pointer) lowering below.  N5008
  // [expr.prim.lambda.closure]/4: the call operator is a template,
  // instantiated for the argument types of each call; the function-pointer
  // lowering fixes every `auto' to `signed int', so a generic lambda passed
  // to a function template (`visit([this](auto &a) {...})') was called through
  // an `int (*)(int &)'.  By-reference captures, including the data members
  // a member-function lambda captures through `this' (Phase E), are reference
  // members of the closure and work in the template operator().
  const bool generic_closure_eligible =
    is_generic_lambda && !lambda_has_explicit_this &&
    !member_context_unsupported && !lambda_body_has_nested_lambda;

  // Collect parameters
  const irept &params_irep = expr.find(ID_parameters);
  code_typet::parameterst func_params;
  for(const auto &p : params_irep.get_sub())
  {
    const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
    // C++23 deducing this: skip explicit object parameter
    if(pdecl.get_bool("explicit_this"))
      continue;
    // N5008 [dcl.fct]/5, [dcl.meaning]: the parameter's type is the
    // decl-specifier type as modified by the declarator -- `int *p' is a
    // pointer, `W *win' likewise.  Taking the decl-specifier type alone
    // dropped every pointer (and array) declarator of a lambda parameter:
    // `[](W *win) { return win->soc; }' saw `win' as a `W' ("operand of
    // unary * is not a pointer", user-reported Issue 11).
    typet ptype = pdecl.declarators().empty()
                    ? pdecl.type()
                    : pdecl.declarators().front().merge_type(pdecl.type());
    typecheck_type(ptype);
    // [dcl.fct]/5: "array of T" / "function returning T" parameters are
    // adjusted to pointers (`int *p[2]' is `int **')
    adjust_function_parameter(ptype);
    irep_idt pname;
    // Per N5008 [dcl.fct]/16: a lambda parameter may be unnamed
    // (e.g. `[](std::size_t) { ... }`).  Probe the declarator
    // structure defensively before reading the identifier.
    if(!pdecl.declarators().empty())
    {
      const auto &name_sub = pdecl.declarators().front().name().get_sub();
      if(!name_sub.empty())
        pname = name_sub.front().get(ID_identifier);
    }
    // Synthesise a unique base_name for unnamed parameters: the
    // downstream scope/parameter machinery requires a non-empty
    // base_name (cpp_scopes.cpp:30 `put_into_scope` precondition).
    if(pname.empty())
      pname = "__unnamed_param_" + std::to_string(func_params.size());
    code_typet::parametert param(ptype);
    param.set_identifier(func_sym_name + "::" + id2string(pname));
    param.set_base_name(pname);
    func_params.push_back(param);
  }

  // Determine return type: use explicit trailing return type if present
  // (and not a generic lambda where the type may reference template params),
  // otherwise deduce from body.
  typet lambda_return_type = signed_int_type();
  bool deduce_return = true;
  {
    const irept &explicit_ret = expr.find(ID_return_type);
    if(explicit_ret.is_not_nil() && !is_generic_lambda)
    {
      lambda_return_type = static_cast<const typet &>(explicit_ret);
      // N5008 [dcl.fct]/8: the parameters are in scope in the trailing
      // return type -- `[](int __s) -> decltype(__s)` must resolve
      // `__s` (cvise-reduced from a preprocessed libc++ <string>
      // seed; previously "symbol '__s' is unknown" dropped the whole
      // enclosing body).  Register the parameters in a scope visible
      // to the return type's type-check.  The parameter symbols
      // proper are created below from func_type; here we install
      // lightweight placeholders keyed by the same identifiers.
      cpp_save_scopet save_scope_for_ret(cpp_scopes);
      cpp_scopet &ret_scope =
        cpp_scopes.current_scope().new_scope(id2string(func_sym_name) + "$ret");
      ret_scope.prefix = id2string(func_sym_name) + "::";
      cpp_scopes.go_to(ret_scope);
      for(const auto &p : func_params)
      {
        if(symbol_table.lookup(p.get_identifier()) == nullptr)
        {
          auxiliary_symbolt psym;
          psym.name = p.get_identifier();
          psym.base_name = p.get_base_name();
          psym.type = p.type();
          psym.mode = ID_cpp;
          psym.module = module;
          psym.location = loc;
          psym.is_lvalue = true;
          symbol_table.insert(psym);
        }
        const symbolt &psym_ref = symbol_table.lookup_ref(p.get_identifier());
        cpp_idt &id = cpp_scopes.put_into_scope(psym_ref);
        id.id_class = cpp_idt::id_classt::SYMBOL;
      }
      typecheck_type(lambda_return_type);
      deduce_return = false;
    }
  }

  code_typet func_type(std::move(func_params), lambda_return_type);

  // Create parameter symbols
  for(const auto &p : func_type.parameters())
  {
    auxiliary_symbolt psym;
    psym.name = p.get_identifier();
    psym.base_name = p.get_base_name();
    psym.type = p.type();
    psym.mode = ID_cpp;
    psym.module = module;
    psym.location = loc;
    psym.is_file_local = true;
    psym.is_thread_local = true;
    psym.is_lvalue = true;
    psym.is_parameter = true;
    symbol_table.insert(std::move(psym));
  }

  // For generic lambdas, try to type-check the body with the default int
  // parameters. If it succeeds, the lambda can be used as a function pointer.
  // If it fails (e.g., body uses struct members), defer to call-site
  // instantiation.  Closure-eligible generic lambdas (Phase F) skip this and
  // are lowered to a closure with a template operator() below.
  if(is_generic_lambda && !generic_closure_eligible)
  {
    codet default_body(ID_nil);
    bool body_ok = false;

    // Save error count so we can restore it if body type-checking fails
    const std::size_t saved_errors =
      get_message_handler().get_message_count(messaget::M_ERROR);
    const unsigned saved_verbosity = get_message_handler().get_verbosity();

    // Suppress error messages during the try
    get_message_handler().set_verbosity(0);

    // Try type-checking with int parameters
    try
    {
      cpp_save_scopet save_scope(cpp_scopes);
      cpp_scopet &lambda_scope =
        cpp_scopes.current_scope().new_scope(lambda_id + "_try");
      lambda_scope.prefix = func_sym_name + "::";
      cpp_scopes.go_to(lambda_scope);

      for(const auto &p : func_type.parameters())
      {
        if(!symbol_table.has_symbol(p.get_identifier()))
        {
          auxiliary_symbolt psym;
          psym.name = p.get_identifier();
          psym.base_name = p.get_base_name();
          psym.type = p.type();
          psym.mode = ID_cpp;
          psym.module = module;
          psym.location = loc;
          psym.is_file_local = true;
          psym.is_thread_local = true;
          psym.is_lvalue = true;
          psym.is_parameter = true;
          symbol_table.insert(std::move(psym));
        }
        const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
        cpp_idt &id = cpp_scopes.put_into_scope(psym);
        id.id_class = cpp_idt::id_classt::SYMBOL;
      }

      // Put captures in scope
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
        {
          if(cap.second.id() == ID_symbol)
          {
            const symbolt &outer_sym = symbol_table.lookup_ref(
              to_symbol_expr(cap.second).get_identifier());
            // N5008 [expr.prim.lambda.capture]/6: an init-capture `[&r =
            // k]' declares `r' as a reference to the initializer; the body
            // names it `r', not `k'.  Enter the outer symbol under the
            // capture's own name.
            if(outer_sym.base_name != cap.first)
            {
              cpp_idt &cid = cpp_scopes.current_scope().insert(cap.first);
              cid.identifier = outer_sym.name;
              cid.id_class = cpp_idt::id_classt::SYMBOL;
              continue;
            }
            cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
            cid.id_class = cpp_idt::id_classt::SYMBOL;
            continue;
          }
        }

        std::string csym_name = func_sym_name + "::" + id2string(cap.first);
        if(!symbol_table.has_symbol(csym_name))
        {
          auxiliary_symbolt csym;
          csym.name = csym_name;
          csym.base_name = cap.first;
          csym.type = cap.second.type();
          csym.value = cap.second;
          csym.mode = ID_cpp;
          csym.module = module;
          csym.location = loc;
          csym.is_file_local = true;
          csym.is_thread_local = true;
          csym.is_lvalue = true;
          csym.is_state_var = true;
          symbol_table.insert(std::move(csym));
        }

        const symbolt &inserted = symbol_table.lookup_ref(csym_name);
        cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
        cid.id_class = cpp_idt::id_classt::SYMBOL;
      }

      default_body = to_code(static_cast<exprt &>(expr.add("body")));

      {
        return_deduction_contextt return_context{*this, func_type, true};
        typecheck_code(default_body);
        return_context.finish();
      }

      // Prepend capture initializations
      if(!capture_values.empty())
      {
        code_blockt block;
        for(const auto &cap : capture_values)
        {
          if(by_ref_captures.count(cap.first))
            continue;
          symbol_exprt cap_sym(
            func_sym_name + "::" + id2string(cap.first), cap.second.type());
          codet assign(ID_assign);
          assign.copy_to_operands(cap_sym);
          assign.copy_to_operands(cap.second);
          assign.add_source_location() = loc;
          block.add(std::move(assign));
        }
        if(default_body.get_statement() == ID_block)
        {
          for(auto &stmt : to_code_block(default_body).statements())
            block.add(std::move(stmt));
        }
        else
          block.add(std::move(default_body));
        default_body = std::move(block);
      }

      body_ok = true;
    }
    catch(...)
    {
      // Body type-checking failed with int params — leave body as nil
      // Restore error count so this doesn't cause overall failure
      get_message_handler().set_message_count(messaget::M_ERROR, saved_errors);
    }

    // Restore verbosity
    get_message_handler().set_verbosity(saved_verbosity);

    // N5008 [expr.prim.lambda.closure]/4: the closure type's function call
    // operator has the lambda's compound-statement as its body, defined
    // once -- here, in place.  Mark it converted like convert_function
    // does; the end-of-unit sweep that completes half-converted
    // system-header bodies would otherwise convert it a second time (see
    // the non-generic path below).
    if(body_ok)
      default_body.set("#cpp_converted", true);
    symbolt func_sym;
    func_sym.name = func_sym_name;
    func_sym.base_name = lambda_id;
    func_sym.type = func_type;
    func_sym.value = body_ok ? static_cast<exprt>(default_body) : nil_exprt();
    func_sym.mode = ID_cpp;
    func_sym.module = module;
    func_sym.location = loc;
    func_sym.is_file_local = true;
    symbol_table.insert(std::move(func_sym));

    {
      const symbolt &fsym = symbol_table.lookup_ref(func_sym_name);
      cpp_idt &fid = cpp_scopes.put_into_scope(fsym);
      fid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    expr = address_of_exprt(symbol_exprt(func_sym_name, func_type));
    expr.type() = pointer_typet(func_type, config.ansi_c.pointer_width);
    expr.add_source_location() = loc;
    return;
  }

  // Type-check the body with captures and params in scope
  codet body_code(ID_nil);
  {
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopet &lambda_scope = cpp_scopes.current_scope().new_scope(lambda_id);
    lambda_scope.prefix = func_sym_name + "::";
    cpp_scopes.go_to(lambda_scope);

    for(const auto &p : func_type.parameters())
    {
      const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
      cpp_idt &id = cpp_scopes.put_into_scope(psym);
      id.id_class = cpp_idt::id_classt::SYMBOL;
    }

    for(const auto &cap : capture_values)
    {
      // By-ref captures: put the outer symbol directly into scope
      if(by_ref_captures.count(cap.first))
      {
        if(cap.second.id() == ID_symbol)
        {
          const symbolt &outer_sym = symbol_table.lookup_ref(
            to_symbol_expr(cap.second).get_identifier());
          // [expr.prim.lambda.capture]/6: `[&r = k]' -- see the non-generic
          // path
          if(outer_sym.base_name != cap.first)
          {
            cpp_idt &cid = cpp_scopes.current_scope().insert(cap.first);
            cid.identifier = outer_sym.name;
            cid.id_class = cpp_idt::id_classt::SYMBOL;
            continue;
          }
          cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
          cid.id_class = cpp_idt::id_classt::SYMBOL;
          continue;
        }
      }

      auxiliary_symbolt csym;
      csym.name = func_sym_name + "::" + id2string(cap.first);
      csym.base_name = cap.first;
      csym.type = cap.second.type();
      csym.value = cap.second;
      csym.mode = ID_cpp;
      csym.module = module;
      csym.location = loc;
      csym.is_file_local = true;
      csym.is_thread_local = true;
      csym.is_lvalue = true;
      csym.is_state_var = true;
      symbol_table.insert(std::move(csym));

      const symbolt &inserted =
        symbol_table.lookup_ref(func_sym_name + "::" + id2string(cap.first));
      cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
      cid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    body_code = to_code(static_cast<exprt &>(expr.add("body")));

    // the lambda body's own return type; the enclosing one is restored at
    // scope exit
    return_deduction_contextt return_context{*this, func_type, deduce_return};

    if(generic_closure_eligible)
    {
      // N5008 [expr.prim.lambda.closure]/4, [temp.inst]/11: the call
      // operator of a generic lambda is a member function TEMPLATE; its body
      // is instantiated only for the argument types it is called with (the
      // closure's template operator(), below).  Type-checking it here with
      // `signed int' for every `auto' -- as the function-pointer lowering
      // did -- instantiated the function templates named in it for int,
      // which no conforming implementation does, and dropped their bodies
      // when ill-formed for int (libstdc++ 13 <format>: __formatter_fp::
      // format for _M_format_arg's visitor).  The lowered function keeps no
      // body, as when that trial failed.
      body_code = codet(ID_nil);
    }
    else
      typecheck_code(body_code);

    return_context.finish();

    // Prepend capture initializations to the body
    if(!capture_values.empty())
    {
      code_blockt block;
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
          continue;
        symbol_exprt cap_sym(
          func_sym_name + "::" + id2string(cap.first), cap.second.type());
        codet assign(ID_assign);
        assign.copy_to_operands(cap_sym);
        assign.copy_to_operands(cap.second);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }
      if(body_code.get_statement() == ID_block)
      {
        for(auto &stmt : to_code_block(body_code).statements())
          block.add(std::move(stmt));
      }
      else
        block.add(std::move(body_code));
      body_code = std::move(block);
    }
  }

  // N5008 [expr.prim.lambda.closure]/4: the body was type-checked in place
  // above; mark it converted like convert_function does.  Without the mark
  // the end-of-unit sweep that completes half-converted system-header
  // bodies (cpp_typecheckt::typecheck) converted the already-converted
  // body a second time, which fails on constructs that are not idempotent
  // under re-conversion -- libc++'s basic_string(basic_string &&)
  // initializes `__r_' through the lambda `[](basic_string &__s) ->
  // decltype(__r_) && { return std::move(__s.__r_); }(__str)': the
  // re-checked `return std::move(...)' saw the call's xvalue result as an
  // lvalue ("invalid implicit conversion from '__compressed_pair &' to
  // '__compressed_pair &&'") and the lambda's body was dropped, leaving a
  // moved-from std::string nondet.
  if(body_code.id() != ID_nil)
    body_code.set("#cpp_converted", true);

  // Create the function symbol
  symbolt func_sym;
  func_sym.name = func_sym_name;
  func_sym.base_name = lambda_id;
  func_sym.type = func_type;
  func_sym.value = body_code;
  func_sym.mode = ID_cpp;
  func_sym.module = module;
  func_sym.location = loc;
  func_sym.is_file_local = true;
  symbol_table.insert(std::move(func_sym));

  {
    const symbolt &fsym = symbol_table.lookup_ref(func_sym_name);
    cpp_idt &fid = cpp_scopes.put_into_scope(fsym);
    fid.id_class = cpp_idt::id_classt::SYMBOL;
  }

  // [expr.prim.lambda.closure]: synthesise the closure class -- a struct with
  // operator() (the body) and, for a captureless non-generic lambda, a
  // non-explicit conversion to pointer-to-function -- and make the lambda
  // expression an object of that class.  This lets the lambda be used as an
  // object (e.g. stored by value in std::function) as well as a function
  // pointer (via the conversion).  A generic lambda's operator() is a member
  // function template (Phase F).
  if(
    !lambda_has_explicit_this && !member_context_unsupported &&
    !lambda_body_has_nested_lambda)
  {
    // The closure type must be identical across repeated type-checks of the
    // same lambda-expression (e.g. during auto return type deduction, which
    // type-checks the body twice, possibly in different scopes).  Key it on
    // the parser's per-lambda number and create it only once.  (The source
    // location is the fallback for a lambda built without the parser; it has
    // no column, so two lambdas on one line would share a closure.)
    // N5008 [expr.prim.lambda.closure]/1, [temp.spec.general]/1: in a
    // template each specialization's lambda-expression is a distinct
    // expression with its own closure type -- the lambda in size_of<long>
    // must not reuse size_of<char>'s, whose operator() was checked with
    // C = char.  The parser's number is shared by the specializations, so
    // the key also names the enclosing scope (the function specialization).
    const std::string loc_key =
      id2string(cpp_scopes.current_scope().prefix) + "#" +
      (expr.find("#lambda_uid").is_not_nil()
         ? "uid:" + id2string(expr.get("#lambda_uid"))
         : id2string(loc.get_file()) + ":" + id2string(loc.get_line()) + ":" +
             id2string(loc.get_column()));
    irep_idt closure_sym_name = lambda_closure_map[loc_key];

    // Collect the by-copy captures in a fixed (sorted) order shared between the
    // closure's data members and the closure object's initialiser.
    std::vector<irep_idt> capture_members;
    for(const auto &cap : capture_values)
      capture_members.push_back(cap.first);

    if(closure_sym_name.empty())
    {
      const std::string closure_tag = lambda_id + "_closure";

      typet closure_struct(ID_struct);
      cpp_namet closure_tag_name;
      closure_tag_name.get_sub().push_back(irept(ID_name));
      closure_tag_name.get_sub().back().set(ID_identifier, closure_tag);
      closure_struct.add(ID_tag) = closure_tag_name;
      closure_struct.add_source_location() = loc;
      auto &body = closure_struct.add(ID_body).get_sub();

      // [expr.prim.lambda.capture]: for each entity captured by copy, an
      // unnamed non-static data member is declared in the closure type,
      // direct-initialised from the entity when the closure object is created;
      // an entity captured by reference is captured as a reference (a reference
      // member that denotes the entity).  We name each member after the
      // captured entity so that odr-uses of the entity in the body resolve to
      // the member by ordinary member lookup.
      for(const auto &name : capture_members)
      {
        cpp_declarationt mem_decl;
        mem_decl.type() = capture_values.at(name).type();
        cpp_declaratort mem_dtor;
        cpp_namet mem_name;
        mem_name.get_sub().push_back(irept(ID_name));
        mem_name.get_sub().back().set(ID_identifier, name);
        mem_dtor.name() = mem_name;
        if(by_ref_captures.count(name))
        {
          // An entity captured by reference is a reference member: a `&` on
          // the declarator over the entity's type.
          typet ref_op(ID_frontend_pointer);
          ref_op.set(ID_C_reference, true);
          mem_dtor.type() = ref_op;
        }
        mem_decl.declarators().push_back(mem_dtor);
        body.push_back(mem_decl);
      }

      // <ret> operator()(<params>) const { <body> }
      {
        cpp_declarationt op_decl;
        cpp_declaratort op_dtor;
        cpp_namet op_name;
        op_name.get_sub().push_back(irept(ID_operator));
        op_name.get_sub().push_back(irept("()"));
        op_dtor.name() = op_name;
        typet op_ftype(ID_function_type);

        if(is_generic_lambda)
        {
          // [expr.prim.lambda.closure]: a generic lambda's operator() is a
          // member function template; each `auto` parameter introduces an
          // invented template type parameter, and a C++20 `[]<typename T>(...)`
          // template-parameter-list names the parameters explicitly.  Rewrite
          // each generic parameter type to reference its type parameter, build
          // the template-parameter list, and make operator() a template with a
          // deduced (auto) return type unless one is given explicitly.
          irept op_params = saved_lambda_parameters;
          irept template_parameters;
          std::set<irep_idt> seen_type_params;
          std::size_t auto_index = 0;
          auto add_type_param = [&](const irep_idt &tpname, bool is_pack)
          {
            if(!seen_type_params.insert(tpname).second)
              return;
            cpp_declarationt tp;
            tp.set(ID_is_type, true);
            tp.type() = typet("cpp-template-type");
            cpp_declaratort tp_dtor;
            cpp_namet tp_name;
            tp_name.get_sub().push_back(irept(ID_name));
            tp_name.get_sub().back().set(ID_identifier, tpname);
            tp_dtor.name() = tp_name;
            // N5008 [dcl.spec.auto.general]/3 + [temp.param]: `auto... xs'
            // invents a template parameter PACK (`template <class... T>
            // operator()(T... xs)'); without the marking the pack accepted
            // exactly one argument.
            if(is_pack)
              tp_dtor.set_has_ellipsis();
            tp.declarators().push_back(tp_dtor);
            template_parameters.get_sub().push_back(irept());
            template_parameters.get_sub().back().swap(tp);
          };
          for(auto &p : op_params.get_sub())
          {
            cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
            if(pdecl.get_bool("explicit_this"))
              continue;
            if(has_auto(pdecl.type()) || pdecl.type().id() == ID_auto)
            {
              const irep_idt tpname =
                "_lambda_tp_" + std::to_string(auto_index++);
              const bool is_pack =
                pdecl.type().get_bool(ID_ellipsis) ||
                (!pdecl.declarators().empty() &&
                 (pdecl.declarators().front().get_bool(ID_ellipsis) ||
                  pdecl.declarators().front().type().get_bool(ID_ellipsis)));
              add_type_param(tpname, is_pack);
              typet cn(ID_cpp_name);
              irept nm(ID_name);
              nm.set(ID_identifier, tpname);
              cn.get_sub().push_back(nm);
              // N5008 [dcl.spec.auto.general]/3: the placeholder is replaced
              // by the invented parameter -- only the `auto' itself, so a
              // `const auto &' parameter stays a reference to const (an
              // rvalue argument binds to it, [dcl.init.ref]/5.3)
              std::function<bool(irept &)> replace_auto = [&](irept &t)
              {
                if(t.id() == ID_auto)
                {
                  // keep the ellipsis marking of an `auto...' pack
                  const bool ellipsis = t.get_bool(ID_ellipsis);
                  t = cn;
                  if(ellipsis)
                    t.set(ID_ellipsis, true);
                  return true;
                }
                bool replaced = false;
                // merged_type / frontend_pointer subtypes (has_auto)
                if(
                  t.id() == ID_merged_type || t.id() == ID_frontend_pointer ||
                  t.id() == ID_pointer)
                {
                  for(auto &sub : t.get_sub())
                    replaced = replace_auto(sub) || replaced;
                }
                return replaced;
              };
              if(!replace_auto(pdecl.type()))
                pdecl.type() = cn;
            }
            else if(
              pdecl.type().id() == ID_cpp_name &&
              !pdecl.type().get_sub().empty())
            {
              add_type_param(
                pdecl.type().get_sub().front().get(ID_identifier), false);
            }
          }
          op_ftype.add(ID_parameters) = op_params;
          if(saved_lambda_return_type.is_not_nil())
            op_decl.type() =
              static_cast<const typet &>(saved_lambda_return_type);
          else
            op_decl.type() = typet(ID_auto);
          typet template_type(ID_template);
          template_type.add(ID_template_parameters).swap(template_parameters);
          op_decl.add(ID_template_type).swap(template_type);
          op_decl.set(ID_is_template, true);
        }
        else
        {
          // The closure's operator() returns the lambda's return type: the
          // explicit trailing return type if given, otherwise the type deduced
          // for the lowered function.  (Lambdas whose body contains a nested
          // lambda -- where that deduced type is not usable -- are excluded
          // from this path above, so this deduced type is reliable here, and
          // using it avoids re-deducing via `auto`, which double-type-checks
          // the body and mishandles reference-member accesses of by-reference
          // captures.)
          // N5008 [dcl.fct]/8: an explicit trailing return type may
          // reference the parameters (`-> decltype(__s)`), which are
          // NOT in scope when the closure class's body converts.  Use
          // the ALREADY-RESOLVED return type (typechecked above with
          // the parameters registered) rather than the raw parse tree.
          op_decl.type() = func_type.return_type();
          op_ftype.add(ID_parameters) = saved_lambda_parameters;
        }
        op_dtor.type() = op_ftype;
        // [expr.prim.lambda.closure]: operator() is const unless the lambda is
        // declared mutable (in which case its by-copy capture members are
        // mutable and modifications persist in the closure object).
        if(!lambda_is_mutable)
          op_dtor.method_qualifier() = typet(ID_const);
        op_dtor.value() = static_cast<const exprt &>(saved_lambda_body);
        if(lambda_needs_this_pointer)
        {
          std::set<irep_idt> parameter_names;
          for(const auto &p : saved_lambda_parameters.get_sub())
          {
            const cpp_declarationt &pdecl =
              static_cast<const cpp_declarationt &>(p);
            if(!pdecl.declarators().empty())
            {
              const auto &n = pdecl.declarators().front().name().get_sub();
              if(n.size() == 1 && n.front().id() == ID_name)
                parameter_names.insert(n.front().get(ID_identifier));
            }
          }
          for(const auto &n : parameter_names)
            lambda_member_function_names.erase(n);
          rewrite_lambda_this_uses(
            op_dtor.value(), lambda_member_function_names);
        }
        op_decl.declarators().push_back(op_dtor);
        body.push_back(op_decl);
      }

      // §7.5.6.2: only a captureless lambda's closure type has a (non-explicit)
      // conversion to pointer-to-function.  Implement it as
      // `operator <fp>() const { return <lowered function>; }`.  (For a generic
      // captureless lambda this conversion is itself a template; not yet
      // synthesised -- such lambdas are still usable as call targets.)
      if(lambda_is_captureless && !is_generic_lambda)
      {
        cpp_declarationt conv_decl;
        conv_decl.type() = typet("cpp-cast-operator");
        cpp_declaratort conv_dtor;
        cpp_namet conv_name;
        conv_name.get_sub().push_back(irept(ID_operator));
        typet fp_type = pointer_typet(func_type, config.ansi_c.pointer_width);
        conv_name.get_sub().push_back(static_cast<const irept &>(fp_type));
        conv_dtor.name() = conv_name;
        typet conv_ftype(ID_function_type);
        conv_ftype.add(ID_parameters);
        conv_dtor.type() = conv_ftype;
        conv_dtor.method_qualifier() = typet(ID_const);
        exprt fn_ref(ID_cpp_name);
        fn_ref.get_sub().push_back(irept(ID_name));
        fn_ref.get_sub().back().set(ID_identifier, lambda_id);
        codet ret_stmt(ID_return);
        ret_stmt.add_to_operands(std::move(fn_ref));
        code_blockt conv_body;
        conv_body.add(std::move(ret_stmt));
        conv_dtor.value() = conv_body;
        conv_decl.declarators().push_back(conv_dtor);
        body.push_back(conv_decl);
      }

      cpp_declarationt closure_declaration;
      closure_declaration.type() = closure_struct;
      convert(closure_declaration);

      closure_sym_name =
        id2string(cpp_scopes.current_scope().prefix) + "tag-" + closure_tag;
      if(!symbol_table.has_symbol(closure_sym_name))
        closure_sym_name.clear();
      else
        lambda_closure_map[loc_key] = closure_sym_name;
    }

    if(!closure_sym_name.empty() && symbol_table.has_symbol(closure_sym_name))
    {
      // Materialise the closure as a temporary object so its address can be
      // formed -- e.g. when bound to std::function's `_Functor&&` parameter --
      // and so member calls can take `this`.  The by-copy capture members are
      // direct-initialised, in member order, from the captured entities'
      // values at this (capture) point.
      struct_tag_typet closure_tag_type(closure_sym_name);
      // The closure object's value has one operand per component of the
      // closure type: the captures by member NAME (the members were
      // declared in capture_members order, but the layout may have inserted
      // padding components between them), everything else zero.
      const struct_typet &closure_struct_type = follow_tag(closure_tag_type);
      auto closure_value_opt = zero_struct_value(closure_tag_type, loc);
      struct_exprt closure_value = closure_value_opt.has_value()
                                     ? *closure_value_opt
                                     : struct_exprt({}, closure_tag_type);
      for(const auto &name : capture_members)
      {
        const exprt &entity = capture_values.at(name);
        exprt value = entity;
        if(by_ref_captures.count(name))
        {
          // [expr.prim.lambda.capture]: bind the reference member to the
          // captured entity (a reference is modelled as the entity's address).
          address_of_exprt addr(entity);
          addr.type() = reference_type(entity.type());
          value = std::move(addr);
        }
        if(!closure_value_opt.has_value())
        {
          closure_value.add_to_operands(std::move(value));
          continue;
        }
        for(const auto &c : closure_struct_type.components())
        {
          if(c.get_base_name() == name && !c.get_is_padding())
          {
            set_struct_member_value(
              closure_value, closure_struct_type, c, std::move(value));
            break;
          }
        }
      }
      side_effect_exprt tmp(ID_temporary_object, closure_tag_type, loc);
      tmp.add_to_operands(std::move(closure_value));
      tmp.set(ID_C_lvalue, true);
      tmp.set(ID_mode, ID_cpp);
      expr.swap(tmp);
      return;
    }
  }

  // Replace the lambda with a function pointer
  expr = address_of_exprt(symbol_exprt(func_sym_name, func_type));
  expr.type() = pointer_typet(func_type, config.ansi_c.pointer_width);
  expr.add_source_location() = loc;
}
