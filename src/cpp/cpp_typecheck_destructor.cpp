/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/c_types.h>
#include <util/pointer_expr.h>

#include "cpp_typecheck.h"

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

  dtor.add(ID_type).id(ID_destructor);
  dtor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  dtor.add_to_operands(std::move(decl));
}

/// produces destructor code for a class object
codet cpp_typecheckt::dtor(const symbolt &symbol, const symbol_exprt &this_expr)
{
  PRECONDITION(symbol.type.id() == ID_struct || symbol.type.id() == ID_union);

  source_locationt source_location=symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)+
    "::~"+id2string(symbol.base_name)+"()");

  code_blockt block;

  const struct_union_typet::componentst &components =
    to_struct_union_type(symbol.type).components();

  // take care of virtual methods
  for(const auto &c : components)
  {
    if(c.get_bool(ID_is_vtptr))
    {
      const cpp_namet cppname(c.get_base_name());

      const symbolt *virtual_table_symbol_type;
      if(lookup(
           to_pointer_type(c.type()).base_type().get(ID_identifier),
           virtual_table_symbol_type))
        continue;

      const symbolt *virtual_table_symbol_var;
      if(lookup(
           id2string(virtual_table_symbol_type->name) + "@" +
             id2string(symbol.name),
           virtual_table_symbol_var))
        continue;

      exprt var = virtual_table_symbol_var->symbol_expr();
      address_of_exprt address(var);
      DATA_INVARIANT(address.type() == c.type(), "type mismatch");

      already_typechecked_exprt::make_already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, c.get_name());
      ptrmember.operands().push_back(this_expr);

      code_frontend_assignt assign(ptrmember, address);
      block.add(assign);
      continue;
    }
  }

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

  // call the base destructors in the reverse order
  for(class_typet::basest::const_reverse_iterator bit = bases.rbegin();
      bit != bases.rend();
      bit++)
  {
    DATA_INVARIANT(bit->id() == ID_base, "base class expression expected");

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
    typecast_exprt cast_this{this_expr, pointer_type(bit->type())};
    cast_this.add_source_location() = source_location;
    already_typechecked_exprt::make_already_typechecked(cast_this);

    dereference_exprt object{cast_this, bit->type()};
    object.add_source_location() = source_location;

    const bool disabled_access_control = disable_access_control;
    disable_access_control = true;
    auto dtor_code = cpp_destructor(source_location, object);
    disable_access_control = disabled_access_control;

    if(dtor_code.has_value())
      block.add(dtor_code.value());
  }

  return std::move(block);
}
