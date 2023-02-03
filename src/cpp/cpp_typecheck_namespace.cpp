/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/source_location.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

void cpp_typecheckt::convert(cpp_namespace_spect &namespace_spec)
{
  // save the scope
  cpp_save_scopet saved_scope(cpp_scopes);

  const irep_idt &name=namespace_spec.get_namespace();

  if(name.empty())
  {
    // "unique namespace"
    error().source_location=namespace_spec.source_location();
    error() << "unique namespace not supported yet" << eom;
    throw 0;
  }

  irep_idt final_name(name);

  std::string identifier=
    cpp_scopes.current_scope().prefix+id2string(final_name);

  symbol_table_baset::symbolst::const_iterator it =
    symbol_table.symbols.find(identifier);

  if(it!=symbol_table.symbols.end())
  {
    if(namespace_spec.alias().is_not_nil())
    {
      error().source_location=namespace_spec.source_location();
      error() << "namespace alias '" << final_name << "' previously declared\n"
              << "location of previous declaration: " << it->second.location
              << eom;
      throw 0;
    }

    if(it->second.type.id()!=ID_namespace)
    {
      error().source_location=namespace_spec.source_location();
      error() << "namespace '" << final_name << "' previously declared\n"
              << "location of previous declaration: " << it->second.location
              << eom;
      throw 0;
    }

    // enter that scope
    cpp_scopes.set_scope(it->first);
  }
  else
  {
    symbolt symbol{identifier, typet(ID_namespace), ID_cpp};
    symbol.base_name=final_name;
    symbol.location=namespace_spec.source_location();
    symbol.module=module;

    if(!symbol_table.insert(std::move(symbol)).second)
    {
      error().source_location=symbol.location;
      error() << "cpp_typecheckt::convert_namespace: symbol_table.move() failed"
              << eom;
      throw 0;
    }

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
    for(auto &item : namespace_spec.items())
      convert(item);
  }
}
