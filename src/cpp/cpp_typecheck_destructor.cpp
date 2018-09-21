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

  irept name;
  name.id(ID_name);
  name.set(ID_identifier, "~"+id2string(symbol.base_name));
  name.set(ID_C_source_location, symbol.location);

  cpp_declaratort decl;
  decl.name().id(ID_cpp_name);
  decl.name().move_to_sub(name);
  decl.type().id(ID_function_type);
  decl.type().subtype().make_nil();

  decl.value().id(ID_code);
  decl.value().add(ID_type).id(ID_code);
  decl.value().set(ID_statement, ID_block);
  decl.add("cv").make_nil();
  decl.add("throw_decl").make_nil();

  dtor.add(ID_type).id(ID_destructor);
  dtor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  dtor.move_to_operands(decl);
}

/// produces destructor code for a class object
///
///    Note:
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
    if(c.get_bool("is_vtptr"))
    {
      exprt name(ID_name);
      name.set(ID_identifier, c.get_base_name());

      cpp_namet cppname;
      cppname.move_to_sub(name);

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
      ptrmember.set(ID_component_name, c.get(ID_name));
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_assignt assign(ptrmember, address);
      block.operands().push_back(assign);
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

    irept name(ID_name);
    name.set(ID_identifier, cit->get_base_name());
    name.set(ID_C_source_location, source_location);

    cpp_namet cppname;
    cppname.get_sub().push_back(name);

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
      block.move_to_operands(dtor_code.value());
  }

  const irept::subt &bases=symbol.type.find(ID_bases).get_sub();

  // call the base destructors in the reverse order
  for(irept::subt::const_reverse_iterator
      bit=bases.rbegin();
      bit!=bases.rend();
      bit++)
  {
    assert(bit->id()==ID_base);
    assert(bit->find(ID_type).id() == ID_symbol_type);
    const symbolt &psymb = lookup(bit->find(ID_type).get(ID_identifier));

    symbol_exprt this_ptr(ID_this, pointer_type(symbol.type));
    dereference_exprt object(this_ptr, psymb.type);
    object.add_source_location() = source_location;

    const bool disabled_access_control = disable_access_control;
    disable_access_control = true;
    auto dtor_code = cpp_destructor(source_location, object);
    disable_access_control = disabled_access_control;

    if(dtor_code.has_value())
      block.move_to_operands(dtor_code.value());
  }

  return block;
}
