/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::find_dtor

  Inputs:

 Outputs:

    Note:

\*******************************************************************/

bool cpp_typecheckt::find_dtor(const symbolt& symbol) const
{
  const irept &components=
    symbol.type.find(ID_components);

  forall_irep(cit, components.get_sub())
  {
    if(cit->get(ID_base_name)=="~"+id2string(symbol.base_name))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: default_dtor

  Inputs:

 Outputs:

 Purpose:

    Note:

\*******************************************************************/

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
  decl.type().id("function_type");
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

/*******************************************************************\

Function: cpp_typecheckt::dtor

  Inputs:

 Outputs:

 Purpose: produces destructor code for a class object

    Note:

\*******************************************************************/

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
  for(struct_union_typet::componentst::const_iterator
      cit=components.begin();
      cit!=components.end();
      cit++)
  {
    if(cit->get_bool("is_vtptr"))
    {
      exprt name(ID_name);
      name.set(ID_identifier, cit->get(ID_base_name));

      cpp_namet cppname;
      cppname.move_to_sub(name);

      const symbolt &virtual_table_symbol_type = 
        namespacet(symbol_table).lookup(
          cit->type().subtype().get(ID_identifier));

      const symbolt &virtual_table_symbol_var  =
        namespacet(symbol_table).lookup(
          id2string(virtual_table_symbol_type.name) + "@" + id2string(symbol.name));

      exprt var=virtual_table_symbol_var.symbol_expr();
      address_of_exprt address(var);
      assert(address.type()==cit->type());

      already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, cit->get(ID_name));
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
    name.set(ID_identifier, cit->get(ID_base_name));
    name.set(ID_C_source_location, source_location);

    cpp_namet cppname;
    cppname.get_sub().push_back(name);

    exprt member(ID_ptrmember);
    member.set("component_cpp_name", cppname);
    member.operands().push_back(exprt("cpp-this"));
    member.add_source_location() = source_location;

    codet dtor_code=
      cpp_destructor(source_location, cit->type(), member);

    if(dtor_code.is_not_nil())
      block.move_to_operands(dtor_code);
  }
  
  const irept::subt &bases=symbol.type.find(ID_bases).get_sub();

  // call the base destructors in the reverse order
  for(irept::subt::const_reverse_iterator
      bit=bases.rbegin();
      bit!=bases.rend();
      bit++)
  {
    assert(bit->id()==ID_base);
    assert(bit->find(ID_type).id()==ID_symbol);
    const symbolt& psymb = lookup(bit->find(ID_type).get(ID_identifier));

    exprt object(ID_dereference);
    object.operands().push_back(exprt("cpp-this"));
    object.add_source_location() = source_location;

    exprt dtor_code =
      cpp_destructor(source_location, psymb.type, object);

    if(dtor_code.is_not_nil())
      block.move_to_operands(dtor_code);
  }

  return block;
}

