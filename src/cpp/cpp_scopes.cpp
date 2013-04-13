/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/i2string.h>

#include "cpp_scopes.h"

/*******************************************************************\

Function: cpp_scopest::new_block_scope

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_scopet &cpp_scopest::new_block_scope()
{
  unsigned prefix=++current_scope().compound_counter;
  cpp_scopet &n=new_scope(i2string(prefix));
  n.id_class=cpp_idt::BLOCK_SCOPE;
  return n;
}

/*******************************************************************\

Function: cpp_scopest::put_into_scope

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_idt &cpp_scopest::put_into_scope(
  const symbolt &symbol,
  cpp_scopet &scope,
  bool is_friend)
{
  assert(!symbol.name.empty());
  assert(!symbol.base_name.empty());

  // functions are also scopes
  if(symbol.type.id()==ID_code)
  {
    cpp_scopest::id_mapt::iterator id_it = id_map.find(symbol.name);
    if(id_it == id_map.end())
    {
      irep_idt block_base_name(std::string("$block:") + symbol.base_name.c_str());
      cpp_idt &id = scope.insert(block_base_name);
      id.id_class=cpp_idt::BLOCK_SCOPE;
      id.identifier=symbol.name;
      id.is_scope=true;
      id.prefix = id2string(scope.prefix) + id2string(symbol.base_name) + "::";
      id_map[symbol.name]=&id;
    }
  }

  // should go away, and be replaced by the 'tag only declaration' rule
  if(is_friend)
  {
    cpp_save_scopet saved_scope(*this);
    go_to(scope);
    go_to_global_scope();

    cpp_idt &id=current_scope().insert(symbol.base_name);
    id.identifier=symbol.name;
    id.id_class = cpp_idt::SYMBOL;
    if(id_map.find(symbol.name)==id_map.end())
      id_map[symbol.name]=&id;
    return id;
  }
  else
  {
    cpp_idt &id=scope.insert(symbol.base_name);
    id.identifier=symbol.name;
    id.id_class = cpp_idt::SYMBOL;
    if(id_map.find(symbol.name)==id_map.end())
      id_map[symbol.name]=&id;
    return id;
  }
}

/*******************************************************************\

Function: cpp_scopest::print_current

  Inputs:

 Outputs:
 Purpose:

\*******************************************************************/

void cpp_scopest::print_current(std::ostream &out) const
{
  const cpp_scopet *scope=current_scope_ptr;

  do
  {
    scope->print_fields(out);
    out << std::endl;
    scope=&scope->get_parent();
  }
  while(!scope->is_root_scope());
}
