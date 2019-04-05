/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifdef DEBUG
#include <iostream>
#endif

#include "cpp_typecheck.h"

void cpp_typecheckt::typecheck_method_bodies()
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  while(!method_bodies.empty())
  {
    // Dangerous not to take a copy here. We'll have to make sure that
    // convert is never called with the same symbol twice.
    method_bodyt &method_body = *method_bodies.begin();
    symbolt &method_symbol = *method_body.method_symbol;

    template_map.swap(method_body.template_map);
    instantiation_stack.swap(method_body.instantiation_stack);

    method_bodies.erase(method_bodies.begin());

    exprt &body=method_symbol.value;
    if(body.id() == ID_cpp_not_typechecked)
      continue;

#ifdef DEBUG
    std::cout << "convert_method_body: " << method_symbol.name << '\n';
    std::cout << "  is_not_nil: " << body.is_not_nil() << '\n';
    std::cout << "  !is_zero: " << (!body.is_zero()) << '\n';
#endif
    if(body.is_not_nil() && !body.is_zero())
      convert_function(method_symbol);
  }

  old_instantiation_stack.swap(instantiation_stack);
}

void cpp_typecheckt::add_method_body(symbolt *_method_symbol)
{
#ifdef DEBUG
  std::cout << "add_method_body: " << _method_symbol->name << '\n';
#endif
  // Converting a method body might add method bodies for methods that we have
  // already analyzed. Adding the same method more than once causes duplicated
  // symbol prefixes, therefore we have to keep track.
  if(methods_seen.insert(_method_symbol->name).second)
  {
    method_bodies.push_back(
      method_bodyt(_method_symbol, template_map, instantiation_stack));
  }
#ifdef DEBUG
  else
    std::cout << "  already exists\n";
#endif
}
