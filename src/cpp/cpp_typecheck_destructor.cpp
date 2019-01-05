/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/c_types.h>

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
  assert(symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_union);

  cpp_declaratort decl;
  decl.name() = cpp_namet("~" + id2string(symbol.base_name), symbol.location);
  decl.type().id(ID_function_type);
  decl.type().subtype().make_nil();

  decl.value().id(ID_code);
  decl.value().add(ID_type).id(ID_code);
  decl.value().set(ID_statement, ID_block);
  decl.add(ID_cv).make_nil();
  decl.add(ID_throw_decl).make_nil();

  dtor.add(ID_type).id(ID_destructor);
  dtor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  dtor.add_to_operands(std::move(decl));
}

/// produces destructor code for a class object
codet cpp_typecheckt::dtor(const symbolt &symbol)
{
  assert(symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_union);

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

      const symbolt &virtual_table_symbol_type =
        lookup(c.type().subtype().get(ID_identifier));

      const symbolt &virtual_table_symbol_var = lookup(
        id2string(virtual_table_symbol_type.name) + "@" +
        id2string(symbol.name));

      exprt var=virtual_table_symbol_var.symbol_expr();
      address_of_exprt address(var);
      assert(address.type() == c.type());

      already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, c.get_name());
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_assignt assign(ptrmember, address);
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

    const cpp_namet cppname(cit->get_base_name(), source_location);

    exprt member(ID_ptrmember, type);
    member.set(ID_component_cpp_name, cppname);
    member.operands().push_back(
      symbol_exprt(ID_this, pointer_type(symbol.type)));
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
    const symbolt &psymb = lookup(bit->type());

    symbol_exprt this_ptr(ID_this, pointer_type(symbol.type));
    dereference_exprt object(this_ptr, psymb.type);
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
