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

    if(method_symbol.name==ID_main)
      add_argc_argv(method_symbol);

    exprt &body=method_symbol.value;
    if(body.id() == ID_cpp_not_typechecked)
      continue;

#ifdef DEBUG
  std::cout << "convert_method_body: " << method_symbol.name << std::endl;
  std::cout << "  is_not_nil: " << body.is_not_nil() << std::endl;
  std::cout << "  !is_zero: " << (!body.is_zero()) << std::endl;
#endif
    if(body.is_not_nil() && !body.is_zero())
      convert_function(method_symbol);
  }

  old_instantiation_stack.swap(instantiation_stack);
}

void cpp_typecheckt::add_method_body(symbolt *_method_symbol)
{
#ifdef DEBUG
  std::cout << "add_method_body: " << _method_symbol->name << std::endl;
#endif

  // We have to prevent the same method to be added multiple times
  //   otherwise we get duplicated symbol prefixes
  if(methods_seen.find(_method_symbol->name) != methods_seen.end())
  {
#ifdef DEBUG
    std::cout << "  already exists" << std::endl;
#endif
    return;
  }
  method_bodies.push_back(
    method_bodyt(_method_symbol, template_map, instantiation_stack));

  // Converting a method body might add method bodies for methods
  // that we have already analyzed. Hence, we have to keep track.
  methods_seen.insert(_method_symbol->name);
}
