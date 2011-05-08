/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <set>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::typcheck_compound_bases

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_compound_bases(struct_typet &type)
{
  std::set<irep_idt> bases;
  std::set<irep_idt> vbases;

  irep_idt default_class_access=
    type.get_bool(ID_C_class)?ID_private:ID_public;
    
  irept::subt &bases_irep=type.add(ID_bases).get_sub();

  Forall_irep(base_it, bases_irep)
  {
    const cpp_namet &name=
      to_cpp_name(base_it->find(ID_name));

    exprt base_symbol_expr=
      resolve(
        name,
        cpp_typecheck_resolvet::TYPE,
        cpp_typecheck_fargst());

    if(base_symbol_expr.id()!=ID_type ||
       base_symbol_expr.type().id()!=ID_symbol)
    {
      err_location(name.location());
      str << "expected type as struct/class base";
      throw 0;
    }

    const symbolt &base_symbol=
      lookup(base_symbol_expr.type());

    if(base_symbol.type.id()==ID_incomplete_struct)
    {
      err_location(name.location());
      str << "base type is incomplete";
      throw 0;
    }
    else if(base_symbol.type.id()!=ID_struct)
    {
      err_location(name.location());
      str << "expected struct or class as base, but got `"
          << to_string(base_symbol.type) << "'";
      throw 0;
    }

    bool virtual_base = base_it->get_bool(ID_virtual);
    irep_idt class_access = base_it->get(ID_protection);

    if(class_access==irep_idt())
      class_access = default_class_access;

    base_symbol_expr.id(ID_base);
    base_symbol_expr.set(ID_access, class_access);

    if(virtual_base)
      base_symbol_expr.set(ID_virtual, true);

    base_it->swap(base_symbol_expr);

    // Add base scopes as parents to the current scope
    cpp_scopes.current_scope().add_secondary_scope(
      static_cast<cpp_scopet &>(*cpp_scopes.id_map[base_symbol.name]));

    const struct_typet &base_struct_type=
      to_struct_type(base_symbol.type);

    add_base_components(
      base_struct_type,
      class_access,
      type,
      bases,
      vbases,
      virtual_base);
  }

  if(!vbases.empty())
  {
    // add a flag to determine
    // if this is the most-derived-object
    struct_typet::componentt most_derived;

    most_derived.type()=bool_typet();
    most_derived.set_access(ID_public);
    most_derived.set(ID_base_name, "@most_derived");
    most_derived.set_name(cpp_identifier_prefix(current_mode)+"::"+
                     cpp_scopes.current_scope().prefix+"::"+"@most_derived");
    most_derived.set(ID_pretty_name, "@most_derived");
    most_derived.location()=type.location();
    put_compound_into_scope(most_derived);

    to_struct_type(type).components().push_back(most_derived);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::add_base_components

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::add_base_components(
  const struct_typet &from,
  const irep_idt &access,
  struct_typet &to,
  std::set<irep_idt> &bases,
  std::set<irep_idt> &vbases,
  bool is_virtual)
{
  const irep_idt &from_name = from.get(ID_name);

  if(is_virtual && vbases.find(from_name)!=vbases.end())
    return;

  if(bases.find(from_name)!=bases.end())
  {
    err_location(to);
    str << "error: non-virtual base class " << from_name
        << " inherited multiple times";
    throw 0;
  }

  bases.insert(from_name);

  if(is_virtual)
    vbases.insert(from_name);

  // look at the the parents of the base type
  forall_irep(it, from.find(ID_bases).get_sub())
  {
    irep_idt sub_access=it->get(ID_access);

    if(access==ID_private)
      sub_access=ID_private;
    else if(access==ID_protected && sub_access!=ID_private)
      sub_access=ID_protected;

    const symbolt &symb=
      lookup(it->find(ID_type).get(ID_identifier));

    bool is_virtual=it->get_bool(ID_virtual);

    // recursive call
    add_base_components(
      to_struct_type(symb.type),
      sub_access,
      to,
      bases,
      vbases,
      is_virtual);
  }

  // add the components
  const struct_typet::componentst &src_c=from.components();
  struct_typet::componentst &dest_c=to.components();

  for(struct_typet::componentst::const_iterator
      it=src_c.begin();
      it!=src_c.end();
      it++)
  {
    if(it->get_bool(ID_from_base))
      continue;

    // copy the component
    dest_c.push_back(*it);
    
    // now twiddle the copy
    struct_typet::componentt &component=dest_c.back();
    component.set(ID_from_base, true);

    irep_idt comp_access=component.get_access();

    if(access==ID_public)
    {
      if(comp_access==ID_private)
        component.set_access("noaccess");
    }
    else if(access == ID_protected)
    {
      if(comp_access==ID_private)
        component.set_access("noaccess");
      else
        component.set_access(ID_private);
    }
    else if(access == ID_private)
    {
      if(comp_access == "noaccess" || comp_access == ID_private)
        component.set_access("noaccess");
      else
        component.set_access(ID_private);
    }
    else
      assert(false);
      
    // put into scope
    
  }
}


