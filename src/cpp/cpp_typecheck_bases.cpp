/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <set>

void cpp_typecheckt::typecheck_compound_bases(struct_typet &type)
{
  std::set<irep_idt> bases;
  std::set<irep_idt> vbases;

  irep_idt default_class_access = type.default_access();

  irept::subt &bases_irep=type.add(ID_bases).get_sub();

  Forall_irep(base_it, bases_irep)
  {
    const cpp_namet &name=
      to_cpp_name(base_it->find(ID_name));

    exprt base_symbol_expr=
      resolve(
        name,
        cpp_typecheck_resolvet::wantt::TYPE,
        cpp_typecheck_fargst());

    if(base_symbol_expr.id()!=ID_type)
    {
      error().source_location=name.source_location();
      error() << "expected type as struct/class base" << eom;
      throw 0;
    }

    // elaborate any class template instances given as bases
    elaborate_class_template(base_symbol_expr.type());

    if(base_symbol_expr.type().id() != ID_symbol_type)
    {
      error().source_location=name.source_location();
      error() << "expected type symbol as struct/class base" << eom;
      throw 0;
    }

    const symbolt &base_symbol =
      lookup(to_symbol_type(base_symbol_expr.type()));

    if(base_symbol.type.id()==ID_incomplete_struct)
    {
      error().source_location=name.source_location();
      error() << "base type is incomplete" << eom;
      throw 0;
    }
    else if(base_symbol.type.id()!=ID_struct)
    {
      error().source_location=name.source_location();
      error() << "expected struct or class as base, but got `"
              << to_string(base_symbol.type) << "'" << eom;
      throw 0;
    }

    bool virtual_base = base_it->get_bool(ID_virtual);
    irep_idt class_access = base_it->get(ID_protection);

    if(class_access.empty())
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
    struct_typet::componentt most_derived(
      cpp_scopes.current_scope().prefix + "::" + "@most_derived", bool_typet());

    most_derived.set_access(ID_public);
    most_derived.set_base_name("@most_derived");
    most_derived.set_pretty_name("@most_derived");
    most_derived.add_source_location()=type.source_location();
    put_compound_into_scope(most_derived);

    to_struct_type(type).components().push_back(most_derived);
  }
}

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
    error().source_location=to.source_location();
    error() << "error: non-virtual base class " << from_name
            << " inherited multiple times" << eom;
    throw 0;
  }

  bases.insert(from_name);

  if(is_virtual)
    vbases.insert(from_name);

  // look at the the parents of the base type
  for(const auto &b : from.bases())
  {
    irep_idt sub_access = b.get(ID_access);

    if(access==ID_private)
      sub_access=ID_private;
    else if(access==ID_protected && sub_access!=ID_private)
      sub_access=ID_protected;

    const symbolt &symb = lookup(to_symbol_type(b.type()).get_identifier());

    const bool is_virtual = b.get_bool(ID_virtual);

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
  struct_typet::componentst &dest_c=to.components();

  for(const auto &c : from.components())
  {
    if(c.get_bool(ID_from_base))
      continue;

    // copy the component
    dest_c.push_back(c);

    // now twiddle the copy
    struct_typet::componentt &component=dest_c.back();
    component.set(ID_from_base, true);

    irep_idt comp_access=component.get_access();

    if(access==ID_public)
    {
      if(comp_access==ID_private)
        component.set_access(ID_noaccess);
    }
    else if(access == ID_protected)
    {
      if(comp_access==ID_private)
        component.set_access(ID_noaccess);
      else
        component.set_access(ID_private);
    }
    else if(access == ID_private)
    {
      if(comp_access == ID_noaccess || comp_access == ID_private)
        component.set_access(ID_noaccess);
      else
        component.set_access(ID_private);
    }
    else
      UNREACHABLE;

    // put into scope
  }
}
