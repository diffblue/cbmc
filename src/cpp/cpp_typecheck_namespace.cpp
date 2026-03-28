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
  cpp_scopet &parent_scope = cpp_scopes.current_scope();

  const irep_idt &name=namespace_spec.get_namespace();

  if(name.empty())
  {
    // Anonymous (unique) namespace — generate a unique name.
    // libc++ uses these in headers like <tuple>.
    static unsigned anon_ns_counter = 0;
    irep_idt anon_name("#anon_ns_" + std::to_string(anon_ns_counter++));

    std::string identifier =
      cpp_scopes.current_scope().prefix + id2string(anon_name);

    if(symbol_table.symbols.find(identifier) == symbol_table.symbols.end())
    {
      symbolt symbol;
      symbol.name = identifier;
      symbol.base_name = anon_name;
      symbol.value.make_nil();
      symbol.type = typet(ID_namespace);
      symbol.mode = ID_cpp;
      symbol.module = module;
      symbol.location = namespace_spec.source_location();
      symbol_table.add(symbol);
    }

    cpp_scopet &ns_scope = cpp_scopes.new_namespace(anon_name);
    ns_scope.prefix = identifier + "::";
    cpp_scopes.go_to(ns_scope);
    // Make the anonymous namespace visible in the parent scope
    // (inline namespace semantics)
    parent_scope.add_using_scope(ns_scope);
    return;
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
    {
      const auto &loc = item.source_location();
      std::string file = id2string(loc.get_file());
      // Fall back to namespace location when item has no source location
      if(file.empty())
        file = id2string(namespace_spec.source_location().get_file());
      bool is_system =
        file.find("/usr/include/") == 0 || file.find("/usr/lib/") == 0;

      if(is_system)
      {
        null_message_handlert null_mh;
        message_handlert &old_mh = get_message_handler();
        set_message_handler(null_mh);
        try
        {
          convert(item);
        }
        catch(...)
        {
        }
        set_message_handler(old_mh);
      }
      else
      {
        convert(item);
      }
    }

    // C++11: inline namespaces make their names visible in the parent
    if(namespace_spec.get_is_inline())
      parent_scope.add_using_scope(cpp_scopes.current_scope());
  }
}
