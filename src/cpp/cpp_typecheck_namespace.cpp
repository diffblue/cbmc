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
    // unique namespace
    err_location(namespace_spec);
    throw "unique namespace not supported yet";
  }

  irep_idt final_name(name);

  std::string identifier=
    cpp_identifier_prefix(current_mode)+"::"+
    cpp_scopes.current_scope().prefix+id2string(final_name);

  contextt::symbolst::const_iterator it=
    context.symbols.find(identifier);

  if(it!=context.symbols.end())
  {
    if(it->second.type.id()!="namespace")
    {
      err_location(namespace_spec);
      str << "symbol `" << final_name << "' previously declared" << std::endl;
      str << "location of previous declaration: "
          << it->second.location << std::endl;
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
    symbol.mode=current_mode;
    symbol.module=module;
    symbol.type=typet("namespace");

    if(context.move(symbol))
      throw "cpp_typecheckt::convert_namespace: context.move() failed";

    cpp_scopes.new_namespace(final_name);
  }

  // do the declarations
  for(cpp_namespace_spect::itemst::iterator
      it=namespace_spec.items().begin();
      it!=namespace_spec.items().end();
      it++)
    convert(*it);
}
