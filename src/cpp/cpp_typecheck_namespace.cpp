/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <location.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert(cpp_namespace_spect &namespace_spec)
{
  // save the scope
  cpp_save_scopet saved_scope(cpp_scopes);

  const irep_idt &name=namespace_spec.get_namespace();

  if(name=="")
  {
    // "unique namespace"
    err_location(namespace_spec);
    throw "unique namespace not supported yet";
  }

  irep_idt final_name(name);

  std::string identifier=
    language_prefix+
    cpp_scopes.current_scope().prefix+id2string(final_name);

  symbol_tablet::symbolst::const_iterator it=
    symbol_table.symbols.find(identifier);

  if(it!=symbol_table.symbols.end())
  {
    if(namespace_spec.alias().is_not_nil())
    {
      err_location(namespace_spec);
      str << "namespace alias `" << final_name 
          << "' previously declared" << std::endl;
      str << "location of previous declaration: "
          << it->second.location;
      throw 0;
    }
  
    if(it->second.type.id()!=ID_namespace)
    {
      err_location(namespace_spec);
      str << "namespace `" << final_name 
          << "' previously declared" << std::endl;
      str << "location of previous declaration: "
          << it->second.location;
      throw 0;
    }

    // enter that scope
    cpp_scopes.set_scope(it->first);
  }
  else
  {
    symbolt symbol;

    symbol.name=identifier;
    symbol.base_name=final_name;
    symbol.value.make_nil();
    symbol.location=namespace_spec.location();
    symbol.mode=ID_cpp;
    symbol.module=module;
    symbol.type=typet(ID_namespace);

    if(symbol_table.move(symbol))
      throw "cpp_typecheckt::convert_namespace: symbol_table.move() failed";

    cpp_scopes.new_namespace(final_name);
  }

  if(namespace_spec.alias().is_not_nil())
  {
    cpp_typecheck_resolvet resolver(*this);
    cpp_scopet &s=resolver.resolve_namespace(namespace_spec.alias());
    cpp_scopes.current_scope().add_using_scope(s);
  }
  else
  {
    // do the declarations
    for(cpp_namespace_spect::itemst::iterator
        it=namespace_spec.items().begin();
        it!=namespace_spec.items().end();
        it++)
      convert(*it);
  }
}
