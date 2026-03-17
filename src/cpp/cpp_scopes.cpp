/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_scopes.h"

#include <util/symbol.h>

#include <ostream>

cpp_scopet &cpp_scopest::new_block_scope()
{
  unsigned prefix=++current_scope().compound_counter;
  return new_scope(std::to_string(prefix), cpp_idt::id_classt::BLOCK_SCOPE);
}

cpp_idt &cpp_scopest::put_into_scope(
  const symbolt &symbol,
  cpp_scopet &scope,
  bool is_friend)
{
  PRECONDITION(!symbol.name.empty());
  PRECONDITION(!symbol.base_name.empty());

  // functions are also scopes
  if(symbol.type.id()==ID_code)
  {
    cpp_scopest::id_mapt::iterator id_it = id_map.find(symbol.name);
    if(id_it == id_map.end())
    {
      irep_idt block_base_name(std::string("$block:")+symbol.base_name.c_str());
      cpp_idt &id = scope.insert(block_base_name);
      id.id_class=cpp_idt::id_classt::BLOCK_SCOPE;
      id.identifier=symbol.name;
      id.is_scope=true;
      id.prefix = id2string(scope.prefix) + id2string(symbol.base_name) + "::";
      id_map[symbol.name]=&id;
    }
  }

  if(is_friend)
  {
    if(scope.is_class())
    {
      // Qualified friend function (e.g., friend ... C::f(...)): the
      // symbol is a member of the target class.  Use a hidden name to
      // avoid ambiguity with the actual class component during name
      // resolution; the id_map entry (from the block scope above)
      // suffices for access checking.
      if(id_map.find(symbol.name) == id_map.end())
      {
        cpp_idt &id = scope.insert(
          irep_idt(std::string("$friend:") + id2string(symbol.base_name)));
        id.identifier = symbol.name;
        id.id_class = cpp_idt::id_classt::SYMBOL;
        id_map[symbol.name] = &id;
        return id;
      }
      return *id_map[symbol.name];
    }

    cpp_idt &id = scope.insert(symbol.base_name);
    id.identifier = symbol.name;
    id.id_class = cpp_idt::id_classt::SYMBOL;
    if(id_map.find(symbol.name) == id_map.end())
      id_map[symbol.name] = &id;
    return id;
  }
  else
  {
    cpp_idt &id=scope.insert(symbol.base_name);
    id.identifier=symbol.name;
    id.id_class = cpp_idt::id_classt::SYMBOL;
    if(id_map.find(symbol.name)==id_map.end())
      id_map[symbol.name]=&id;
    return id;
  }
}

void cpp_scopest::print_current(std::ostream &out) const
{
  const cpp_scopet *scope=current_scope_ptr;

  do
  {
    scope->print_fields(out);
    out << '\n';
    scope=&scope->get_parent();
  }
  while(!scope->is_root_scope());
}
