/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/c_types.h>
#include <util/pointer_expr.h>

#include "cpp_typecheck.h"

#include <algorithm>
#include <functional>

bool cpp_typecheckt::find_dtor(const symbolt &symbol) const
{
  for(const auto &c : to_struct_type(symbol.type).components())
  {
    if(c.get_base_name() == "~" + id2string(symbol.base_name))
      return true;
  }

  return false;
}

/// Note:
void cpp_typecheckt::default_dtor(
  const symbolt &symbol,
  cpp_declarationt &dtor)
{
  PRECONDITION(symbol.type.id() == ID_struct || symbol.type.id() == ID_union);

  cpp_declaratort decl;
  decl.name() = cpp_namet("~" + id2string(symbol.base_name), symbol.location);
  decl.type().id(ID_function_type);
  decl.type().add_subtype().make_nil();

  decl.value() = code_blockt();
  decl.add(ID_cv).make_nil();
  decl.add(ID_throw_decl).make_nil();

  // [class.dtor]/8: mark implicitly-declared destructor (trivial candidate).
  decl.type().set("#is_implicit_dtor", true);

  dtor.add(ID_type).id(ID_destructor);
  dtor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  dtor.add_to_operands(std::move(decl));
}

/// produces destructor code for a class object
codet cpp_typecheckt::dtor(
  const symbolt &symbol,
  const symbol_exprt &this_expr,
  codet &prologue)
{
  PRECONDITION(symbol.type.id() == ID_struct || symbol.type.id() == ID_union);

  source_locationt source_location=symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)+
    "::~"+id2string(symbol.base_name)+"()");

  code_blockt block;

  const struct_union_typet::componentst &components =
    to_struct_union_type(symbol.type).components();

  std::list<irep_idt> vbase_ids;
  if(symbol.type.id() == ID_struct)
    get_virtual_bases(to_struct_type(symbol.type), vbase_ids);
  const bool has_virtual_bases = !vbase_ids.empty();

  // take care of virtual methods: the vtables of this class as the complete
  // object.  A class with virtual bases does so only in the complete-object
  // destructor (D1, `@most_derived'); its base-object destructor (D2) keeps
  // the most derived object's tables, whose virtual-base offsets the bodies
  // below rely on (Itanium C++ ABI 5.1.4; see full_member_initialization).
  code_blockt vptr_block;
  for(const auto &c : components)
  {
    if(c.get_bool(ID_is_vtptr))
    {
      // the vtable of the most derived class sharing this pointer
      exprt address = vtable_pointer_value(symbol, c);
      if(address.is_nil())
        continue;
      DATA_INVARIANT(address.type() == c.type(), "type mismatch");

      already_typechecked_exprt::make_already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, c.get_name());
      ptrmember.set("#complete_object", true);
      ptrmember.operands().push_back(this_expr);

      code_frontend_assignt assign(ptrmember, address);
      vptr_block.add(assign);
      continue;
    }
  }
  // N5008 [class.cdtor]/4: a virtual call from the destructor's body
  // dispatches to THIS class's overriders -- the pointers are installed on
  // entry, before the body (the prologue), not after it.
  if(has_virtual_bases)
  {
    prologue = code_ifthenelset(
      cpp_namet("@most_derived").as_expr(), std::move(vptr_block));
  }
  else
    prologue = std::move(vptr_block);

  // call the data member destructors in the reverse order
  for(struct_union_typet::componentst::const_reverse_iterator
      cit=components.rbegin();
      cit!=components.rend();
      cit++)
  {
    const typet &type=cit->type();

    if(cit->get_bool(ID_from_base) ||
       cit->get_bool(ID_is_type) ||
       cit->get_bool(ID_is_static) ||
       type.id()==ID_code ||
       is_reference(type) ||
       cpp_is_pod(type))
      continue;

    // N5008 [class.dtor]/13: a destructor destroys the direct non-variant
    // non-static data members; every member of a union is a variant member
    // ([class.union.general]/1), so a union's destructor -- and with it an
    // anonymous union's ([class.union.anon]/1) -- destroys none of them.
    if(symbol.type.id() == ID_union)
      continue;

    // Anonymous components (padding, unnamed unions in some error-
    // recovery paths) have no base_name; skip rather than
    // synthesising a ptrmember with an empty component name, which
    // would later fail as `'' is not static member` when the
    // member-expression is type-checked.
    if(cit->get_base_name().empty())
      continue;

    // Anonymous components (padding, unnamed unions in some error-
    // recovery paths) have no base_name; skip rather than
    // synthesising a ptrmember with an empty component name, which
    // would later fail as `'' is not static member` when the
    // member-expression is type-checked.
    if(cit->get_base_name().empty())
      continue;

    // Per [class.dtor]/13 a destructor may be invoked on a const
    // or volatile subobject, but CBMC's implicit_typecast path
    // rejects the pointer conversion from `const T*` (the address
    // of a const member) to `T*` (the destructor's `this`
    // parameter).  Until the implicit cv-cast is implemented,
    // skip synthesising the destructor call for const / volatile
    // members.  The memory of the member is still reclaimed via
    // the enclosing object's stack/heap lifetime; omitting the
    // dtor side effect is conservative for assertion checking.
    if(
      cit->type().get_bool(ID_C_constant) ||
      cit->type().get_bool(ID_C_volatile))
      continue;

    const cpp_namet cppname(cit->get_base_name(), source_location);

    exprt member(ID_ptrmember, cit->type());
    member.set(ID_component_cpp_name, cppname);
    member.operands().push_back(this_expr);
    member.add_source_location() = source_location;

    const bool disabled_access_control = disable_access_control;
    disable_access_control = true;
    auto dtor_code = cpp_destructor(source_location, member);
    disable_access_control = disabled_access_control;

    if(dtor_code.has_value())
      block.add(dtor_code.value());
  }

  if(symbol.type.id() == ID_union)
    return std::move(block);

  const auto &bases = to_struct_type(symbol.type).bases();

  // the destructor call for the base subobject of class `base_type' at
  // `this' (the address adjusted by the subobject's offset, for a virtual
  // base the one of this complete object -- N5008 [class.dtor]/14 only has
  // the most derived class's destructor destroy the virtual bases, after the
  // direct non-virtual ones)
  const auto destroy_base = [&](const typet &base_type) -> std::optional<codet>
  {
    // Cast `this_expr` to a `Base*` before dereferencing.  Without
    // the explicit cast, `c_typecheck_baset::typecheck_expr_dereference`
    // (called when `cpp_destructor` builds a member-call expression
    // on `object`) overrides the dereference's type with the
    // pointer's base-type — which is the DERIVED class, not this
    // base subobject.  Subsequent unqualified lookup of `~Base`
    // from the derived-class scope would then walk every base
    // subobject's secondary scope and surface a spurious
    // "symbol '~X' does not uniquely resolve" with siblings whose
    // `base_name` matches but `tag` differs (e.g.,
    // `_Hashtable_ebo_helper<0, _Hash>` vs
    // `_Hashtable_ebo_helper<1, _Equal>` in libstdc++'s
    // `_Hashtable_base`).
    //
    // The cast forces the dereference's type to remain the specific
    // base subobject's class type, pinning member-access lookup to
    // its own scope.  Mark the cast as already-type-checked so the
    // operand walk doesn't undo it.
    exprt cast_this = this_expr;
    make_ptr_typecast(
      cast_this,
      pointer_type(base_type),
      /*static_virtual_base_offset=*/true,
      /*direct_base=*/true);
    cast_this.add_source_location() = source_location;
    already_typechecked_exprt::make_already_typechecked(cast_this);

    dereference_exprt object{cast_this, base_type};
    object.add_source_location() = source_location;

    const bool disabled_access_control = disable_access_control;
    disable_access_control = true;
    auto dtor_code = cpp_destructor(
      source_location, object, /*force_direct=*/true, /*base_subobject=*/true);
    disable_access_control = disabled_access_control;
    return dtor_code;
  };

  // call the direct non-virtual base destructors in the reverse order
  for(class_typet::basest::const_reverse_iterator bit = bases.rbegin();
      bit != bases.rend();
      bit++)
  {
    DATA_INVARIANT(bit->id() == ID_base, "base class expression expected");
    if(bit->get_bool(ID_virtual))
      continue;

    // Itanium C++ ABI 2.6.2 / N5008 [class.cdtor]/4: a base with virtual
    // bases is destroyed under this complete object's construction vtables
    // (see full_member_initialization)
    if(bit->type().id() == ID_struct_tag)
    {
      code_blockt installs;
      for(auto &install : construction_vtable_installs(
            symbol, to_struct_tag_type(bit->type()).get_identifier()))
      {
        already_typechecked_exprt::make_already_typechecked(install.second);
        exprt ptrmember(ID_ptrmember);
        ptrmember.set(ID_component_name, install.first.get_name());
        ptrmember.set("#complete_object", true);
        ptrmember.operands().push_back(this_expr);
        installs.add(code_frontend_assignt(ptrmember, install.second));
      }
      if(!installs.statements().empty())
      {
        block.add(code_ifthenelset(
          cpp_namet("@most_derived").as_expr(), std::move(installs)));
      }
    }

    auto dtor_code = destroy_base(bit->type());
    if(dtor_code.has_value())
      block.add(dtor_code.value());
  }

  // then, in the complete-object destructor only, the virtual bases in the
  // reverse of their construction order (a virtual base after those whose
  // hierarchy contains it -- the reverse of full_member_initialization)
  if(has_virtual_bases)
  {
    std::list<irep_idt> construction_order;
    std::function<void(const irep_idt &)> add_vbase =
      [&](const irep_idt &vbase_id)
    {
      if(
        std::find(
          construction_order.begin(), construction_order.end(), vbase_id) !=
        construction_order.end())
        return;
      const symbolt &symb = lookup(vbase_id);
      if(symb.type.id() == ID_struct)
      {
        std::list<irep_idt> own;
        get_virtual_bases(to_struct_type(symb.type), own);
        for(const auto &o : own)
          add_vbase(o);
      }
      construction_order.push_back(vbase_id);
    };
    for(const auto &v : vbase_ids)
      add_vbase(v);

    code_blockt vbase_block;
    for(auto it = construction_order.rbegin(); it != construction_order.rend();
        ++it)
    {
      auto dtor_code = destroy_base(struct_tag_typet(*it));
      if(dtor_code.has_value())
        vbase_block.add(dtor_code.value());
    }
    block.add(code_ifthenelset(
      cpp_namet("@most_derived").as_expr(), std::move(vbase_block)));
  }

  return std::move(block);
}
